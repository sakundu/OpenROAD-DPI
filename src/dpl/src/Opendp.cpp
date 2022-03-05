/////////////////////////////////////////////////////////////////////////////
// Original authors: SangGi Do(sanggido@unist.ac.kr), Mingyu
// Woo(mwoo@eng.ucsd.edu)
//          (respective Ph.D. advisors: Seokhyeong Kang, Andrew B. Kahng)
// Rewrite by James Cherry, Parallax Software, Inc.
//
// Copyright (c) 2019, The Regents of the University of California
// Copyright (c) 2018, SangGi Do and Mingyu Woo
// All rights reserved.
//
// BSD 3-Clause License
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice, this
//   list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
//
// * Neither the name of the copyright holder nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
///////////////////////////////////////////////////////////////////////////////

#include "dpl/Opendp.h"

#include <cfloat>
#include <cmath>
#include <limits>
#include <map>
#include <vector>

#include "Graphics.h"
#include "dbTransform.h"
#include "ord/OpenRoad.hh"  // closestPtInRect
#include "utl/Logger.h"

namespace dpl {

using std::round;
using std::string;
using std::vector;

using utl::DPL;

using odb::dbBox;
using odb::dbBPin;
using odb::dbBTerm;
using odb::dbITerm;
using odb::dbMasterType;
using odb::dbMPin;
using odb::dbMTerm;
using odb::dbNet;
using odb::dbOrientType;
using odb::dbPlacementStatus;
using odb::dbSigType;
using odb::dbTransform;
using odb::Point;
using odb::Rect;

Cell::Cell() :
  db_inst_(nullptr),
  x_(0),
  y_(0),
  width_(0),
  height_(0),
  is_placed_(false),
  hold_(false),
  group_(nullptr),
  region_(nullptr)
{
}

const char *
Cell::name() const
{
  return db_inst_->getConstName();
}

int64_t
Cell::area() const
{
  dbMaster *master = db_inst_->getMaster();
  return master->getWidth() * master->getHeight();
}

//////////////////////// DP Improver ////////////////////////////

Move::Move(float Movementt, float deltaa, bool flipp) :
  movement(Movementt),
  delta(deltaa),
  flip(flipp)
{
}

Move::Move() :
  movement(0),
  delta(INT_MAX),
  flip(false)
{
}

dpRow::dpRow() :
  x_(0),
  y_(0)
{
}

dpRow::dpRow(dbRow *row, Rect core_) :
  x_(0),
  y_(0)
{
  Rect rowBox;
  row->getBBox(rowBox);
  int y_ = rowBox.yMin();
  int x_ = rowBox.xMin();
  x_ -= core_.xMin();
  y_ -= core_.yMin();
}

dpRow::dpRow(int x, int y) :
  x_(x),
  y_(y)
{
}

Cell_RPA::Cell_RPA() :
  db_inst_(nullptr),
  x_(0),
  y_(0),
  width_(0),
  height_(0),
  is_placed_(false),
  hold_(false),
  group_(nullptr),
  region_(nullptr),
  rpa(0)
{
}

const char *
Cell_RPA::name_RPA() const
{
  return db_inst_->getConstName();
}

int64_t
Cell_RPA::area_RPA() const
{
  dbMaster *master = db_inst_->getMaster();
  return master->getWidth() * master->getHeight();
}

Pin_RPA::Pin_RPA()
{
}

AccessPoint::AccessPoint()
{
}

///////////// RPA Data Structure //////////////////
PinRPA::PinRPA() :
  mterm_(nullptr),
  internal_rpa_value_(0.0),
  actual_rpa_value_(0.0),
  is_boundary_(false),
  llx_(0),
  lly_(0),
  urx_(0),
  ury_(0)
{
}

CellRPA::CellRPA() :
  db_inst_(nullptr),
  is_flipped_(false),
  llx_(0),
  lly_(0),
  width_(0),
  height_(0),
  ioc_(0.0)
{
}
////////////////////////////////////////////////////////////////

static bool
comparator3(const dpRow *lhs, const dpRow *rhs)
{
  if (lhs->y_ < rhs->y_) {
    return true;
  }
  else if (lhs->y_ == rhs->y_) {
    if (lhs->x_ < rhs->x_)
      return true;
  }
  return false;
}

static bool
comparator6(const Pin_RPA lhs, const Pin_RPA rhs)
{
  return lhs.x_min < rhs.x_min;
}

static bool
comparator4(const AccessPoint lhs, const AccessPoint rhs)
{
  return lhs.x < rhs.x;
}

static bool
comparator5(const AccessPoint lhs, const AccessPoint rhs)
{
  return lhs.y < rhs.y;
}

bool
Opendp::isFixed(const Cell *cell) const
{
  return cell == &dummy_cell_ || cell->db_inst_->isFixed();
}

bool
Opendp::isMultiRow(const Cell *cell) const
{
  auto iter = db_master_map_.find(cell->db_inst_->getMaster());
  assert(iter != db_master_map_.end());
  return iter->second.is_multi_row_;
}

Power
Opendp::topPower(const Cell *cell) const
{
  auto iter = db_master_map_.find(cell->db_inst_->getMaster());
  assert(iter != db_master_map_.end());
  return iter->second.top_power_;
}

////////////////////////////////////////////////////////////////

Group::Group() :
  util(0.0)
{
}

Opendp::Opendp() :
  pad_left_(0),
  pad_right_(0),
  max_displacement_x_(0),
  max_displacement_y_(0),
  grid_(nullptr)
{
  dummy_cell_.is_placed_ = true;
}

Opendp::~Opendp()
{
  deleteGrid();
}

void
Opendp::init(dbDatabase *db,
             Logger *logger)
{
  db_ = db;
  logger_ = logger;
}

void
Opendp::initBlock()
{
  block_ = db_->getChip()->getBlock();
  block_->getCoreArea(core_);
}

void
Opendp::setPaddingGlobal(int left,
                         int right)
{
  pad_left_ = left;
  pad_right_ = right;
}

void
Opendp::setPadding(dbInst *inst,
                   int left,
                   int right)
{
  inst_padding_map_[inst] = std::make_pair(left, right);
}

void
Opendp::setPadding(dbMaster *master,
                   int left,
                   int right)
{
  master_padding_map_[master] = std::make_pair(left, right);
}

bool
Opendp::havePadding() const
{
  return pad_left_ > 0 || pad_right_ > 0 || !master_padding_map_.empty() || !inst_padding_map_.empty();
}

void
Opendp::setDebug(bool displacement,
                 float min_displacement,
                 const dbInst *debug_instance)
{
  if (Graphics::guiActive()) {
    graphics_ = std::make_unique<Graphics>(this,
                                           min_displacement,
                                           debug_instance);
  }
}

void
Opendp::updateRow(vector<vector<CellRPA *>> &all,
                  vector<CellRPA> &tmpCells_, vector<dpRow *> &sortedRows)
{
  // sort(tmpCells_.begin(), tmpCells_.end(), &comparator1);
  int cellCount = <int>tmpCells_.size();
  int i = 0;
  int rowSize = sortedRows.size();

  vector<CellRPA *> row;
  int j = 0;
  int db_row_miny = sortedRows[j]->y_;
  int db_row_maxx = sortedRows[j]->x_;
  j++;

  i = 0;
  CellRPA *temp = &tmpCells_[i];
  i++;

  while (i <= cellCount && j <= rowSize) {
    if (db_row_miny != temp->lly_ || i == cellCount) {
      if (db_row_miny == temp->lly_ && i == cellCount) {
        row.push_back(temp);
      } else if (db_row_miny != temp->lly_ && i == cellCount) {
        row.clear();
        row.push_back(temp);
        all.push_back(row);
        break;
      }

      auto compareLambda1 = [](const CellRPA *lhs, const CellRPA *rhs) {
        return lhs->llx_ < rhs->llx_;
      };

      sort(row.begin(), row.end(), compareLambda1);
      vector<CellRPA *> tmprow;
      int rowLength = row.size();
      int k = 0;

      while (k <= rowLength) {
        if (k < rowLength && row[k]->llx_ < db_row_maxx) {
          tmprow.push_back(row[k]);
          k++;
        } else {
          all.push_back(tmprow);
          tmprow.clear();

          if (k == rowLength || j == rowSize) {
            // logger_->report("Test that it breaks from row");
            break;
          }
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
      }

      row.clear();
      while (db_row_miny != temp->lly_ && i < cellCount && j < rowSize) {
        while (db_row_miny < temp->lly_) {
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
        while (temp->lly_ < db_row_miny) {
          dbMaster *tmpMaster = temp->db_inst_->getMaster();
          logger_->report("Row Y and Cell Y not Matching: Cell Master Name:{:s}",
                          tmpMaster->getName());
          temp = &tmpCells_[i];
          i++;
        }
      }
      if (i == cellCount) {
        break;
      }
    }
    row.push_back(temp);
    temp = &tmpCells_[i];
    i++;
  }
  while (j == rowSize && i < cellCount) {
    temp = &tmpCells_[i];
    dbMaster *tmpMaster = temp->db_inst_->getMaster();
    logger_->report("Cells not able to find any valid row Cell:{:s} X:{:d} Y:{:d}",
                    tmpMaster->getName(),
                    temp->llx_,
                    temp->lly_);
    i++;
  }
  // logger_->report("Update Row is Finished");
}

void
Opendp::updateRow(vector<vector<Cell_RPA *>> &all, vector<Cell_RPA> &tmpCells_,
                  vector<dpRow *> &sortedRows)
{
  //sort(tmpCells_.begin(), tmpCells_.end(), &comparator1);
  int cellCount = (int)tmpCells_.size();
  int i = 0;
  int rowSize = sortedRows.size();

  vector<Cell_RPA *> row;
  int j = 0;
  int db_row_miny = sortedRows[j]->y_;
  int db_row_maxx = sortedRows[j]->x_;
  j++;

  i = 0;
  Cell_RPA *temp = &tmpCells_[i];
  i++;

  while (i <= cellCount && j <= rowSize) {
    if (db_row_miny != temp->y_ || i == cellCount) {
      if (db_row_miny == temp->y_ && i == cellCount) {
        row.push_back(temp);
      } else if (db_row_miny != temp->y_ && i == cellCount) {
        row.clear();
        row.push_back(temp);
        all.push_back(row);
        break;
      }

      auto compareLambda1 = [](const Cell_RPA *lhs, const Cell_RPA *rhs) {
        return lhs->x_ < rhs->x_;
      };

      sort(row.begin(), row.end(), compareLambda1);
      vector<Cell_RPA *> tmprow;
      int rowLength = row.size();
      int k = 0;

      while (k <= rowLength) {
        if (k < rowLength && row[k]->x_ < db_row_maxx) {
          tmprow.push_back(row[k]);
          k++;
        } else {
          all.push_back(tmprow);
          tmprow.clear();

          if (k == rowLength || j == rowSize) {
            // logger_->report("Test that it breaks from row");
            break;
          }
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
      }

      row.clear();
      while (db_row_miny != temp->y_ && i < cellCount && j < rowSize) {
        while (db_row_miny < temp->y_) {
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
        while (temp->y_ < db_row_miny) {
          dbMaster *tmpMaster = temp->db_inst_->getMaster();
          logger_->report("Row Y and Cell Y not Matching: Cell Master Name:{:s}",
                          tmpMaster->getName());
          temp = &tmpCells_[i];
          i++;
        }
      }
      if (i == cellCount) {
        break;
      }
    }
    row.push_back(temp);
    temp = &tmpCells_[i];
    i++;
  }
  while (j == rowSize && i < cellCount) {
    temp = &tmpCells_[i];
    dbMaster *tmpMaster = temp->db_inst_->getMaster();
    logger_->report("Cells not able to find any valid row Cell:{:s} X:{:d} Y:{:d}",
                    tmpMaster->getName(),
                    temp->x_,
                    temp->y_);
    i++;
  }
  // logger_->report("Update Row is Finished");
}

/*
Cell_RPA -> inst
         -> pins
pins -> shape -> APS
*/

void
Opendp::GenerateAP(int dint)
{
  std::map<odb::dbTechLayer *, vector<int>> pin_layer_track_details;
  for (CellRPA &cell : cellrpas_) {
    int px;
    int py;
    cell.db_inst_->getOrigin(px, py);
    dbOrientType orient = cell.db_inst_->getOrient();
    Point origin = Point(px, py);
    dbTransform inst_xfm(orient, origin);

    odb::dbMaster *master = cell.db_inst_->getMaster();
    for (dbMTerm *mterm : master->getMTerms()) {
      // No need to find access point for power pins
      if (mterm->getSigType().isSupply())
        continue;

      cell.pins_.push_back(PinRPA());
      PinRPA &newPin = cell.pins_.back();
      int llx_ = INT_MAX, lly_ = INT_MAX, urx_ = INT_MIN, ury_ = INT_MIN;
      newPin.mterm_ = mterm;
      for (dbMPin *mpin : mterm->getMPins()) {
        odb::dbSet<odb::dbBox> pinshapes = mpin->getGeometry();
        for (odb::dbBox *pinshape : pinshapes) {
          Rect shapeBox;
          pinshape->getBox(shapeBox);
          inst_xfm.apply(shapeBox);
          odb::dbTechLayer *pinLayer = pinshape->getTechLayer();
          odb::dbTechLayerType lType = pinLayer->getType();

          if (lType == odb::dbTechLayerType::Value::ROUTING) {
            // Check if the pin track details is available or not
            if (!pin_layer_track_details.count(pinLayer)) {
              // Find the upper pin layer
              odb::dbTechLayer *upperPinLayer = pinLayer->getUpperLayer();
              while (upperPinLayer->getType() != odb::dbTechLayerType::Value::ROUTING)
                upperPinLayer = upperPinLayer->getUpperLayer();
              odb::dbTrackGrid *tmpGrid = block_->findTrackGrid(upperPinLayer);
              vector<int> xgrid, ygrid;
              tmpGrid->getGridX(xgrid);
              tmpGrid->getGridY(ygrid);
              int xstart = xgrid[0];
              int xpitch = xgrid[1] - xgrid[0];
              int xcount = xgrid.size();
              int ystart = ygrid[0];
              int ypitch = ygrid[1] - ygrid[0];
              int ycount = ygrid.size();
              pin_layer_track_details[pinLayer] = {xstart, xpitch, xcount, ystart, ypitch, ycount};
            } if ((shapeBox.xMax() - shapeBox.xMin()) <= (shapeBox.yMax() - shapeBox.yMin())) {
              // Check if the shape is vertical or horizontal
              // For Vertical Pin Shapes
              int top = shapeBox.yMax();
              int bot = shapeBox.yMin();
              int x = (shapeBox.xMax() + shapeBox.xMin()) / 2;

              llx_ = std::min(x, llx_);
              urx_ = std::max(x, urx_);

              int yoffset = pin_layer_track_details[pinLayer][3];
              int ypitch = pin_layer_track_details[pinLayer][4];

              int count = (top - yoffset) / ypitch;
              int actualTop = (count * ypitch) + yoffset;

              ury_ = std::max(actualTop, ury_);

              for (int i = actualTop; i >= bot; i -= ypitch) {
                AccessPoint ap;
                ap.x = x - cell.llx_ - core_.xMin();
                ap.y = i - cell.lly_;
                ap.layer = pinLayer;
                newPin.ap_list_.push_back(ap);
              }
              lly_ = std::min(lly_, newPin.ap_list_.back().y) + cell.lly_;
            }
          }
        }
      }
      sort(newPin.ap_list_.begin(), newPin.ap_list_.end(), &comparator4);
      newPin.llx_ = llx_ - cell.llx_ - core_.xMin();
      newPin.lly_ = lly_ - cell.lly_ - core_.yMin();
      newPin.urx_ = urx_ - cell.llx_ - core_.xMin();
      newPin.ury_ = ury_ - cell.lly_ - core_.yMin();

      // Check if the pin is boundary or not
      if (newPin.llx_ < dint || cell.width_ - newPin.urx_ < dint) {
        newPin.is_boundary_ = true;
      }
    }

    // x + cell.llx_ , x + w - cell.ll_x
    cell.l2r_.clear();
    cell.r2l_.clear();

    for (PinRPA &pin : cell.pins_) {
      PinRPA *tmp_pin = &pin;
      cell.l2r_.push_back(tmp_pin);
      cell.r2l_.push_back(tmp_pin);
    }

    auto compare_l2r = [](PinRPA *lh, PinRPA *rh) {
      return lh->llx_ < rh->llx_;
    };

    auto compare_r2l = [](PinRPA *lh, PinRPA *rh) {
      return lh->llx_ > rh->llx_;
    };

    sort(cell.l2r_.begin(), cell.l2r_.end(), compare_l2r);
    sort(cell.r2l_.begin(), cell.r2l_.end(), compare_r2l);
  }
}

void
Opendp::GenerateAP()
{
  for (Cell_RPA &cell : cell_rpas_) {
    int px;
    int py;
    cell.db_inst_->getOrigin(px, py);
    dbOrientType orient = cell.db_inst_->getOrient();
    Point origin = Point(px, py);
    dbTransform inst_xfm(orient, origin);

    odb::dbMaster *master = cell.db_inst_->getMaster();
    for (dbMTerm *mterm : master->getMTerms()) {
      // No need to find access point for power pins
      if (mterm->getSigType().isSupply())
        continue;

      for (dbMPin *mpin : mterm->getMPins()) {
        odb::dbSet<odb::dbBox> pinshapes = mpin->getGeometry();
        odb::Rect pinbox = mpin->getBBox();
        inst_xfm.apply(pinbox);
        Pin_RPA newPin;
        newPin.mpin = mpin;
        newPin.x_min = pinbox.xMin();

        for (odb::dbBox *pinshape : pinshapes) {
          Rect shapeBox;
          pinshape->getBox(shapeBox);
          inst_xfm.apply(shapeBox);
          odb::dbTechLayer *pinLayer = pinshape->getTechLayer();
          odb::dbTechLayerType lType = pinLayer->getType();

          if (lType == odb::dbTechLayerType::Value::ROUTING) {
            // Find the upper pin layer
            odb::dbTechLayer *upperPinLayer = pinLayer->getUpperLayer();
            while (upperPinLayer->getType() != odb::dbTechLayerType::Value::ROUTING) {
              upperPinLayer = upperPinLayer->getUpperLayer();
            }

            odb::dbTrackGrid *tmpGrid = block_->findTrackGrid(upperPinLayer);
            vector<int> xgrid, ygrid;

            // vector<pair<int,int>> APs;

            tmpGrid->getGridX(xgrid);
            tmpGrid->getGridY(ygrid);

            // check if the shape is vertical or horizontal
            if ((shapeBox.xMax() - shapeBox.xMin()) <= (shapeBox.yMax() - shapeBox.yMin())) {
              // For Vertical Pin Shapes
              int top = shapeBox.yMax();
              int bot = shapeBox.yMin();
              int ygap = ygrid[1] - ygrid[0];
              int x = (shapeBox.xMax() + shapeBox.xMin()) / 2;

              int count = (top - ygrid[0]) / ygap;
              int actualTop = (count * ygap) + ygrid[0];

              for (int i = actualTop; i >= bot; i -= ygap) {
                AccessPoint ap;
                ap.x = x;
                ap.y = i;
                ap.layer = pinLayer;
                // We do not store vertical AP in xAPs.
                newPin.xAPs.push_back(ap);
                newPin.yAPs.push_back(ap);
              }
            } else {
            }
          }
        }

        // After adding all the APS from each shape, sort them
        sort(newPin.xAPs.begin(), newPin.xAPs.end(), &comparator4);
        sort(newPin.yAPs.begin(), newPin.yAPs.end(), &comparator5);

        cell.pins.push_back(newPin);
      }
    }

    // after adding all the pins
    sort(cell.pins.begin(), cell.pins.end(), &comparator6);
  }
}

void
Opendp::ComputeRPA(int dint, vector<vector<CellRPA *>> &cell_rpas)
{
  // RPA Computation starts
  for (int i = 0; i < cell_rpas.size(); i++) {
    for (int j = 0; j < cell_rpas[i].size(); j++) {
      string cell_name = cell_rpas[i][j]->db_inst_->getName();

      for (int k = 0; k < cell_rpas[i][j]->pins_.size(); k++) {
        // If pin do not have any access point add penalty
        int ap_count = cell_rpas[i][j]->l2r_[k]->ap_list_.size();
        if (ap_count == 0) {
          cell_rpas[i][j]->l2r_[k]->internal_rpa_value_ = -2;
          cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ = -2;
        } else {
          cell_rpas[i][j]->l2r_[k]->internal_rpa_value_ = ap_count;
          cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ = ap_count;
        }

        // First compute Internal RPA value
        for (AccessPoint &ap_main : cell_rpas[i][j]->l2r_[k]->ap_list_) {
          // First Check the Left Neighboring internal pins
          for (int l = k - 1; l >= 0; l--) {
            float neighbor_ap_count = 0;

            if ((ap_main.x - cell_rpas[i][j]->l2r_[l]->urx_) > dint)
              continue;

            for (AccessPoint &ap_neighbor :
                cell_rpas[i][j]->l2r_[l]->ap_list_) {
              if ((std::abs(ap_main.x - ap_neighbor.x) <= dint) &&
                  (ap_main.y == ap_neighbor.y) &&
                  (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            cell_rpas[i][j]->l2r_[k]->internal_rpa_value_ -=
              neighbor_ap_count / cell_rpas[i][j]->l2r_[l]->ap_list_.size();
          }

          // Second Check the right neighboring internal pins
          for (int l = k + 1; l < cell_rpas[i][j]->l2r_.size(); l++) {
            float neighbor_ap_count = 0;

            if ((cell_rpas[i][j]->l2r_[l]->llx_ - ap_main.x) > dint)
              continue;

            for (AccessPoint &ap_neighbor :
                cell_rpas[i][j]->l2r_[l]->ap_list_) {
              if ((std::abs(ap_main.x - ap_neighbor.x) <= dint) &&
                  (ap_main.y == ap_neighbor.y) &&
                  (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            cell_rpas[i][j]->l2r_[k]->internal_rpa_value_ -=
                neighbor_ap_count / cell_rpas[i][j]->l2r_[l]->ap_list_.size();
          }
        }

        // Update the actual rpa_values
        cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ =
            cell_rpas[i][j]->l2r_[k]->internal_rpa_value_;
        if (!cell_rpas[i][j]->l2r_[k]->is_boundary_) {
          continue;
        }

        // Compute w.r.t the neighbor
        for (AccessPoint &ap_main : cell_rpas[i][j]->l2r_[k]->ap_list_) {
          // Update Pin Access Point for Left neightbor
          for (int l = 0; j - 1 >= 0 && l < cell_rpas[i][j - 1]->r2l_.size(); l++) {
            if (((cell_rpas[i][j]->llx_ + ap_main.x) -
                (cell_rpas[i][j - 1]->r2l_[l]->urx_ +cell_rpas[i][j - 1]->llx_)) > dint)
              continue;

            float neighbor_ap_count = 0;
            for (AccessPoint &ap_neighbor : cell_rpas[i][j - 1]->r2l_[l]->ap_list_) {
              if ((std::abs(cell_rpas[i][j]->llx_ +
                  ap_main.x - ap_neighbor.x - cell_rpas[i][j - 1]->llx_) <= dint) &&
                  (ap_main.y == ap_neighbor.y) && (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ -=
                neighbor_ap_count / cell_rpas[i][j - 1]->r2l_[l]->ap_list_.size();
          }

          // Updated Access Point RPA for Right Neighbor
          for (int l = 0; j + 1 < cell_rpas[i].size() && l < cell_rpas[i][j + 1]->l2r_.size(); l++) {
            if (((cell_rpas[i][j + 1]->l2r_[l]->llx_ + cell_rpas[i][j + 1]->llx_) -
                (cell_rpas[i][j]->llx_ + ap_main.x)) > dint)
              continue;

            float neighbor_ap_count = 0;
            for (AccessPoint &ap_neighbor : cell_rpas[i][j + 1]->l2r_[l]->ap_list_) {
              if ((std::abs(cell_rpas[i][j]->llx_ + ap_main.x - ap_neighbor.x -
                  cell_rpas[i][j + 1]->llx_) <= dint) && (ap_main.y == ap_neighbor.y) &&
                  (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ -=
                neighbor_ap_count / cell_rpas[i][j + 1]->l2r_[l]->ap_list_.size();
          }
        }
        cell_rpas[i][j]->ioc_ += (cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ - 1 < 0) ?
            cell_rpas[i][j]->l2r_[k]->actual_rpa_value_ - 1 : 0;
      }
    }
  }
  // Updating all the access point w.r.t block
  // for (int i = 0; i < cell_rpas.size(); i++) {
  //   for (int j = 0; j < cell_rpas[i].size(); j++) {
  //     for(int k = 0; k < cell_rpas[i][j]->pins_.size(); k++) {
  //       for ( AccessPoint &ap: cell_rpas[i][j]->pins_[k].ap_list_ ) {
  //         ap.x += cell_rpas[i][j]->llx_;
  //         ap.y += cell_rpas[i][j]->lly_;
  //       }
  //     }
  //   }
  // }
}

void
Opendp::rpaSwapIncrementUpdate(vector<CellRPA> sub_row, int start_index, int end_index,
                              int main_index, Move *move, int dint)
{
  for (int i = start_index; i <= end_index; i++) {
    int llx = sub_row[i].llx_;
    int lly = sub_row[i].lly_;
    bool is_flipped = sub_row[i].is_flipped_;

    if (i == main_index) {
      llx += move->movement;
      is_flipped = is_flipped != move->flip ? true : false;
      sub_row[i].llx_ = llx;
      sub_row[i].is_flipped_ = is_flipped;
    }

    sub_row[i].ioc_ = 0;
    for (int k = 0; k < sub_row[i].pins_.size(); k++) {
      sub_row[i].pins_[k].actual_rpa_value_ = sub_row[i].pins_[k].internal_rpa_value_;

      if (!sub_row[i].pins_[k].is_boundary_)
        continue;

      for (AccessPoint ap_main : sub_row[i].l2r_[k]->ap_list_) {
        int apx = is_flipped ? llx + sub_row[i].width_ - ap_main.x : llx + ap_main.x;

        // Check Left Neighbor
        for (int l = 0; i - 1 >= 0 && l < sub_row[i - 1].r2l_.size(); l++) {
          int pin_rightx = sub_row[i - 1].is_flipped_ ? sub_row[i - 1].llx_ +
              sub_row[i - 1].width_ - sub_row[i].r2l_[l]->llx_ :
              sub_row[i - 1].r2l_[l]->urx_ + sub_row[i - 1].llx_;
          if ((apx - pin_rightx) > dint)
            continue;

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : sub_row[i - 1].r2l_[l]->ap_list_) {
            int neighbor_apx = sub_row[i - 1].is_flipped_ ? sub_row[i - 1].llx_ +
                sub_row[i - 1].width_ - ap_neighbor.x : sub_row[i - 1].llx_ + ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          sub_row[i].pins_[k].actual_rpa_value_ -=
              neighbor_ap_count / sub_row[i - 1].r2l_[l]->ap_list_.size();
        }

        // Check right neighbor
        for (int l = 0; i + 1 < sub_row.size() && sub_row[i + 1].l2r_.size(); l++) {
          int pin_leftx = sub_row[i + 1].is_flipped_ ? sub_row[i + 1].llx_ +
              sub_row[i + 1].width_ - sub_row[i].l2r_[l]->urx_ :
              sub_row[i + 1].r2l_[l]->urx_ + sub_row[i + 1].llx_;
          if ((pin_leftx - apx) > dint)
            continue;

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : sub_row[i + 1].l2r_[l]->ap_list_) {
            int neighbor_apx = sub_row[i + 1].is_flipped_ ? sub_row[i + 1].llx_ +
                sub_row[i + 1].width_ - ap_neighbor.x : sub_row[i + 1].llx_ + ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          sub_row[i].pins_[k].actual_rpa_value_ -= neighbor_ap_count /
              sub_row[i - 1].r2l_[l]->ap_list_.size();
        }
      }
      sub_row[i].ioc_ += sub_row[i].pins_[k].actual_rpa_value_ - 1 < 0 ?
          sub_row[i].pins_[k].actual_rpa_value_ - 1 : 0;
    }
  }
}

float
Opendp::rpaSwapIncrementHelp(vector<CellRPA> sub_row, int start_index,
                            int end_index, int main_index, Move *move, int dint)
{
  float init_ioc = 0;
  float final_ioc = 0;

  for (int i = start_index; i <= end_index; i++) {
    init_ioc += sub_row[i].ioc_;
  }

  for (int i = start_index; i <= end_index; i++) {
    int llx = sub_row[i].llx_;
    int lly = sub_row[i].lly_;
    bool is_flipped = sub_row[i].is_flipped_;

    if (i == main_index) {
      llx = move->movement;
      is_flipped = is_flipped != move->flip ? true : false;
    }

    float cell_ioc = 0;
    for (int k = 0; k < sub_row[i].pins_.size(); k++) {
      float pin_rpa = sub_row[i].pins_[k].internal_rpa_value_;

      if (!sub_row[i].pins_[k].is_boundary_)
        continue;

      for (AccessPoint ap_main : sub_row[i].l2r_[k]->ap_list_) {
        int apx = is_flipped ? llx + sub_row[i].width_ - ap_main.x : llx + ap_main.x;

        // Check Left Neighbor
        for (int l = 0; i - 1 >= 0 && l < sub_row[i - 1].r2l_.size(); l++) {
          int pin_rightx = sub_row[i - 1].is_flipped_ ? sub_row[i - 1].llx_
              + sub_row[i - 1].width_ - sub_row[i].r2l_[l]->llx_ :
              sub_row[i - 1].r2l_[l]->urx_ + sub_row[i - 1].llx_;
          if ((apx - pin_rightx) > dint)
            continue;

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : sub_row[i - 1].r2l_[l]->ap_list_) {
            int neighbor_apx = sub_row[i - 1].is_flipped_ ? sub_row[i - 1].llx_ +
                sub_row[i - 1].width_ - ap_neighbor.x : sub_row[i - 1].llx_ + ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / sub_row[i - 1].r2l_[l]->ap_list_.size();
        }

        // Check right neighbor
        for (int l = 0; i + 1 < sub_row.size() && l < sub_row[i + 1].l2r_.size(); l++) {
          int pin_leftx = sub_row[i + 1].is_flipped_ ? 
              sub_row[i + 1].llx_ + sub_row[i + 1].width_ -
              sub_row[i].l2r_[l]->urx_ : sub_row[i + 1].r2l_[l]->urx_ + sub_row[i + 1].llx_;
          if ((pin_leftx - apx) > dint)
            continue;

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : sub_row[i + 1].l2r_[l]->ap_list_) {
            int neighbor_apx = sub_row[i + 1].is_flipped_ ?
                sub_row[i + 1].llx_ + sub_row[i + 1].width_ -
                ap_neighbor.x : sub_row[i + 1].llx_ + ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / sub_row[i - 1].r2l_[l]->ap_list_.size();
        }
      }
      cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
    }
    final_ioc += cell_ioc;
  }
  return final_ioc - init_ioc;
}

void
Opendp::rpaIncrementUpdate(int start_index, int end_index, int row_index, int dint)
{
  start_index = start_index >= 0 ? start_index : 0;
  end_index = end_index < cellrpas_row_[row_index].size() ?
      end_index : cellrpas_row_[row_index].size() - 1;

  for (int i = start_index; i <= end_index; i++) {
    float cell_ioc = 0;
    int main_shiftx = cellrpas_row_[row_index][i]->is_flipped_ ?
        cellrpas_row_[row_index][i]->llx_ + cellrpas_row_[row_index][i]->width_:
        cellrpas_row_[row_index][i]->llx_;
    int main_multix = cellrpas_row_[row_index][i]->is_flipped_ ? -1 : 1;

    for (int k = 0; k < cellrpas_row_[row_index][i]->pins_.size(); k++) {
      float pin_rpa = cellrpas_row_[row_index][i]->l2r_[k]->internal_rpa_value_;

      if (!cellrpas_row_[row_index][i]->l2r_[k]->is_boundary_) {
        cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
        continue;
      }

      for (AccessPoint ap_main : cellrpas_row_[row_index][i]->l2r_[k]->ap_list_) {
        int apx = main_shiftx + main_multix * ap_main.x;

        // Check Left Neighbor
        int neighbor_shiftx, neighbor_multix;
        if (i - 1 >= 0) {
          neighbor_shiftx = cellrpas_row_[row_index][i - 1]->is_flipped_ ?
              cellrpas_row_[row_index][i - 1]->llx_ + cellrpas_row_[row_index][i - 1]->width_:
              cellrpas_row_[row_index][i - 1]->llx_;
          neighbor_multix = cellrpas_row_[row_index][i - 1]->is_flipped_ ? -1 : 1;
        }

        for (int l = 0; i - 1 >= 0 && l < cellrpas_row_[row_index][i - 1]->r2l_.size(); l++) {
          int pin_rightx = neighbor_multix == 1 ? cellrpas_row_[row_index][i - 1]->r2l_[l]->urx_ :
              cellrpas_row_[row_index][i - 1]->r2l_[l]->llx_;
          pin_rightx = neighbor_shiftx + neighbor_multix * pin_rightx;
          if (std::abs(apx - pin_rightx) > dint) {
            continue;
          }

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : cellrpas_row_[row_index][i - 1]->r2l_[l]->ap_list_) {
            int neighbor_apx = neighbor_shiftx + neighbor_multix * ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / cellrpas_row_[row_index][i - 1]->r2l_[l]->ap_list_.size();
        }

        // Check right neighbor
        if (i + 1 < cellrpas_row_[row_index].size()) {
          neighbor_shiftx = cellrpas_row_[row_index][i + 1]->is_flipped_ ? 
              cellrpas_row_[row_index][i + 1]->llx_ + cellrpas_row_[row_index][i + 1]->width_ :
              cellrpas_row_[row_index][i + 1]->llx_;
          neighbor_multix = cellrpas_row_[row_index][i + 1]->is_flipped_ ? -1 : 1;
        }

        for (int l = 0; i + 1 < cellrpas_row_[row_index].size() && l <
            cellrpas_row_[row_index][i + 1]->l2r_.size(); l++) {
          int pin_leftx = neighbor_multix == 1 ?
              cellrpas_row_[row_index][i + 1]->l2r_[l]->llx_ :
              cellrpas_row_[row_index][i + 1]->l2r_[l]->urx_;
          pin_leftx = neighbor_shiftx + neighbor_multix * pin_leftx;

          if (std::abs(pin_leftx - apx) > dint) {
            continue;
          }

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : cellrpas_row_[row_index][i + 1]->l2r_[l]->ap_list_) {
            int neighbor_apx = neighbor_shiftx + neighbor_multix * ap_neighbor.x;

            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / cellrpas_row_[row_index][i + 1]->l2r_[l]->ap_list_.size();
        }
      }
      cellrpas_row_[row_index][i]->l2r_[k]->actual_rpa_value_ = pin_rpa;
      cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
    }
    cellrpas_row_[row_index][i]->ioc_ = cell_ioc;
  }
}

float
Opendp::rpaIncrementHelp(int start_index, int end_index, int row_index, int dint, int isReport)
{
  float final_ioc = 0;
  for (int i = start_index; i <= end_index; i++) {
    float cell_ioc = 0;
    int main_shiftx = cellrpas_row_[row_index][i]->is_flipped_ ?
        cellrpas_row_[row_index][i]->llx_ + cellrpas_row_[row_index][i]->width_:
        cellrpas_row_[row_index][i]->llx_;
    int main_multix = cellrpas_row_[row_index][i]->is_flipped_ ? -1 : 1;

    for (int k = 0; k < cellrpas_row_[row_index][i]->pins_.size(); k++) {
      float pin_rpa = cellrpas_row_[row_index][i]->l2r_[k]->internal_rpa_value_;

      if (!cellrpas_row_[row_index][i]->l2r_[k]->is_boundary_) {
        cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
        if (isReport == 1) {
          string pinName = cellrpas_row_[row_index][i]->l2r_[k]->mterm_->getName();
          logger_->report("Pin Name:{:s} New RPA:{:f} Old RPA:{:f} Internal RPA:{:f}",
                          pinName,
                          pin_rpa,
                          cellrpas_row_[row_index][i]->l2r_[k]->actual_rpa_value_,
                          cellrpas_row_[row_index][i]->l2r_[k]->internal_rpa_value_);
        }
        continue;
      }

      for (AccessPoint ap_main : cellrpas_row_[row_index][i]->l2r_[k]->ap_list_) {
        int apx = main_shiftx + main_multix * ap_main.x;

        // Check Left Neighbor
        int neighbor_shiftx, neighbor_multix;
        if (i - 1 >= 0) {
          neighbor_shiftx = cellrpas_row_[row_index][i - 1]->is_flipped_ ?
          cellrpas_row_[row_index][i - 1]->llx_ +
          cellrpas_row_[row_index][i - 1]->width_ :
          cellrpas_row_[row_index][i - 1]->llx_;
          neighbor_multix = cellrpas_row_[row_index][i - 1]->is_flipped_ ? -1 : 1;
        }

        for (int l = 0; i - 1 >= 0 && l < cellrpas_row_[row_index][i - 1]->r2l_.size(); l++) {
          int pin_rightx = neighbor_multix == 1 ? cellrpas_row_[row_index][i - 1]->r2l_[l]->urx_ :
              cellrpas_row_[row_index][i - 1]->r2l_[l]->llx_;
          pin_rightx = neighbor_shiftx + neighbor_multix * pin_rightx;
          if (std::abs(apx - pin_rightx) > dint) {
            if (isReport == 1) {
              string pin_name = cellrpas_row_[row_index][i - 1]->r2l_[l]->mterm_->getName();
              logger_->report("Left Neighbour Pin:{:s} Right Checker AP_MAINX:{:d} APX:{:d}
                              RightX:{:d} Width:{:d} Multi:{:d} Shift:{:d}",
                              pin_name,
                              ap_main.x,
                              apx,
                              pin_rightx,
                              cellrpas_row_[row_index][i]->width_,
                              main_multix,
                              main_shiftx);
            }
            continue;
          }

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : cellrpas_row_[row_index][i - 1]->r2l_[l]->ap_list_) {
            int neighbor_apx = neighbor_shiftx + neighbor_multix * ap_neighbor.x;
            if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y) &&
                (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / cellrpas_row_[row_index][i - 1]->r2l_[l]->ap_list_.size();
          if (isReport == 1) {
            string pin_name = cellrpas_row_[row_index][i - 1]->r2l_[l]->mterm_->getName();
            logger_->report("Left Neighbor Pin:{:s} Ratio:{:f}", pin_name,
                neighbor_ap_count/cellrpas_row_[row_index][i - 1]->r2l_[l]->ap_list_.size());
          }
        }

        // Check right neighbor
        if (i + 1 < cellrpas_row_[row_index].size()) {
          neighbor_shiftx = cellrpas_row_[row_index][i + 1]->is_flipped_ ? 
              cellrpas_row_[row_index][i + 1]->llx_ +
              cellrpas_row_[row_index][i + 1]->width_ :
              cellrpas_row_[row_index][i + 1]->llx_;
          neighbor_multix = cellrpas_row_[row_index][i + 1]->is_flipped_ ? -1 : 1;
        }

        for (int l = 0; i + 1 < cellrpas_row_[row_index].size() &&
            l < cellrpas_row_[row_index][i + 1]->l2r_.size(); l++) {
          int pin_leftx = neighbor_multix == 1 ?
              cellrpas_row_[row_index][i + 1]->l2r_[l]->llx_ :
              cellrpas_row_[row_index][i + 1]->l2r_[l]->urx_;
          pin_leftx = neighbor_shiftx + neighbor_multix * pin_leftx;
          if (std::abs(pin_leftx - apx) > dint) {
            if (isReport == 1) {
              string pin_name = cellrpas_row_[row_index][i + 1]->l2r_[l]->mterm_->getName();
              logger_->report("Right Neighbour Pin:{:s} Right Checker AP_MAINX:{:d}
                              APX:{:d} RightX:{:d} Width:{:d} Multi:{:d} Shift:{:d}",
                              pin_name,
                              ap_main.x,
                              apx,
                              pin_leftx,
                              cellrpas_row_[row_index][i]->width_,
                              main_multix,
                              main_shiftx);
            }
            continue;
          }

          float neighbor_ap_count = 0;
          for (AccessPoint &ap_neighbor : cellrpas_row_[row_index][i + 1]->l2r_[l]->ap_list_) {
            int neighbor_apx = neighbor_shiftx + neighbor_multix * ap_neighbor.x;

            if ((std::abs(apx - neighbor_apx) <= dint) &&
                (ap_main.y == ap_neighbor.y) && (ap_main.layer == ap_neighbor.layer))
              neighbor_ap_count += 1;
          }
          pin_rpa -= neighbor_ap_count / cellrpas_row_[row_index][i + 1]->l2r_[l]->ap_list_.size();
          if (isReport == 1) {
            string pin_name = cellrpas_row_[row_index][i + 1]->l2r_[l]->mterm_->getName();
            logger_->report("Right Neighbor Pin:{:s} Ratio:{:f}", pin_name,
                neighbor_ap_count / cellrpas_row_[row_index][i + 1]->l2r_[l]->ap_list_.size());
          }
        }
      }
      if (isReport == 1) {
        string pinName = cellrpas_row_[row_index][i]->l2r_[k]->mterm_->getName();
        logger_->report("Pin Name:{:s} New RPA:{:f} Old RPA:{:f} Internal RPA:{:f}",
                        pinName,
                        pin_rpa,
                        cellrpas_row_[row_index][i]->l2r_[k]->actual_rpa_value_,
                        cellrpas_row_[row_index][i]->l2r_[k]->internal_rpa_value_);
      }
      cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
    }
    if (isReport == 1) {
      string cellName = cellrpas_row_[row_index][i]->db_inst_->getName();
      logger_->report("Cell Name: {:s} Previous IOC:{:f} New IOC:{:f} Loc:{:d}",
                      cellName,
                      cellrpas_row_[row_index][i]->ioc_,
                      cell_ioc,
                      cellrpas_row_[row_index][i]->llx_);
    }
    final_ioc += cell_ioc;
  }
  return final_ioc;
}

void
Opendp::rpaSwapIncrement(vector<CellRPA *> row, int indexA, int indexB,
                         vector<Move *> moves, int dint)
{
  vector<int> testRow;
  int indexMain = indexA;
  int indexOther = indexB;
  if (indexA < indexB) {
    if (indexA > 0) {
      testRow.push_back(indexA - 1);
    }
    testRow.push_back(indexB);
    if ((indexB - indexA) == 1) {
      testRow.push_back(indexA);
    } else if ((indexB - indexA) == 2) {
      testRow.push_back(indexA + 1);
      testRow.push_back(indexA);
    } else if ((indexB - indexA) == 3) {
      testRow.push_back(indexA + 1);
      testRow.push_back(indexB - 1);
      testRow.push_back(indexA);
    } else {
      testRow.push_back(indexA + 1);
      testRow.push_back(indexB - 1);
      testRow.push_back(indexA);
    }
    if ((indexB + 1) < row.size())
      testRow.push_back(indexB + 1);
  } else {
    // indexA > indexB
    if (indexB > 0) {
      testRow.push_back(indexB - 1);
    } else {
    }
    testRow.push_back(indexA);
    if ((indexA - indexB) == 1) {
      testRow.push_back(indexB);
    } else if ((indexA - indexB) == 2) {
      testRow.push_back(indexB + 1);
      testRow.push_back(indexB);
    } else if ((indexA - indexB) == 3) {
      testRow.push_back(indexB + 1);
      testRow.push_back(indexA - 1);
      testRow.push_back(indexB);
    } else {
      testRow.push_back(indexB + 1);
      testRow.push_back(indexA - 1);
      testRow.push_back(indexB);
    }
    if ((indexA + 1) < row.size())
      testRow.push_back(indexA + 1);
  }

  // std::swap(row[indexA], row[indexB]);

  CellRPA *swap_cell = row[indexA];
  row[indexA] = row[indexB];
  row[indexB] = swap_cell;

  indexMain = indexB;
  indexOther = indexA;

  for (Move *move : moves) {
    int mainCellX = 0;
    int mainCellY = 0;
    int otherCellX = 0;
    int otherCellY = 0;
    row[indexMain]->db_inst_->getLocation(mainCellX, mainCellX);
    row[indexOther]->db_inst_->getLocation(otherCellX, otherCellY);
    int deltaMoveMain = move->movement - mainCellX;
    int deltaOther = mainCellX - otherCellX;
    if (move->flip == false) {
      for (PinRPA *pin : row[indexMain]->l2r_) {
        for (AccessPoint ap : pin->ap_list_) {
          ap.x += deltaMoveMain;
        }
      }
    } else {
      for (PinRPA *pin : row[indexMain]->r2l_) {
        for (AccessPoint ap : pin->ap_list_) {
          ap.x = row[indexMain]->llx_ + row[indexMain]->width_ -
                (ap.x - row[indexMain]->llx_) + deltaMoveMain;
        }
      }
    }
    for (PinRPA *pin : row[indexOther]->l2r_) {
      for (AccessPoint ap : pin->ap_list_) {
        ap.x += deltaOther;
      }
    }

    for (int i = 0; i < testRow.size(); i++) {
      string cell_name = row[testRow[i]]->db_inst_->getName();

      int llx = row[testRow[i]]->llx_;
      int lly = row[testRow[i]]->lly_;
      bool is_flipped = row[testRow[i]]->is_flipped_;

      if (testRow[i] == indexMain) {
        llx = move->movement;
        is_flipped = is_flipped != move->flip ? true : false;
      }

      float cell_ioc = 0;
      for (int k = 0; k < row[testRow[i]]->pins_.size(); k++) {
        float pin_rpa = row[testRow[i]]->pins_[k].internal_rpa_value_;

        if (!row[testRow[i]]->pins_[k].is_boundary_)
          continue;

        for (AccessPoint ap_main : row[testRow[i]]->l2r_[k]->ap_list_) {
          int apx = ap_main.x;

          // Check Left Neighbor
          for (int l = 0; i - 1 >= 0 && l < row[testRow[i] - 1]->r2l_.size(); l++) {
            float neighbor_ap_count = 0;
            for (AccessPoint &ap_neighbor : row[testRow[i] - 1]->r2l_[l]->ap_list_) {
              int neighbor_apx = ap_neighbor.x;
              if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y)
                  && (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            pin_rpa -= neighbor_ap_count / row[testRow[i] - 1]->r2l_[l]->ap_list_.size();
          }

          // Check right neighbor
          for (int l = 0; i + 1 < row.size() && row[testRow[i] + 1]->l2r_.size(); l++) {
            float neighbor_ap_count = 0;
            for (AccessPoint &ap_neighbor : row[testRow[i] + 1]->l2r_[l]->ap_list_) {
              int neighbor_apx = ap_neighbor.x;
              if ((std::abs(apx - neighbor_apx) <= dint) && (ap_main.y == ap_neighbor.y)
                  && (ap_main.layer == ap_neighbor.layer))
                neighbor_ap_count += 1;
            }
            pin_rpa -= neighbor_ap_count / row[testRow[i] + 1]->r2l_[l]->ap_list_.size();
          }
        }
        cell_ioc += pin_rpa - 1 < 0 ? pin_rpa - 1 : 0;
      }
      move->delta += row[testRow[i]]->ioc_ - cell_ioc;
    }

    // change x back after computation
    if (move->flip == false) {
      for (PinRPA *pin : row[indexMain]->l2r_) {
        for (AccessPoint ap : pin->ap_list_) {
          ap.x -= deltaMoveMain;
        }
      }
    } else {
      for (PinRPA *pin : row[indexMain]->r2l_) {
        for (AccessPoint ap : pin->ap_list_) {
          ap.x = row[indexMain]->llx_ + row[indexMain]->width_ -
                (ap.x - row[indexMain]->llx_) - deltaMoveMain;
        }
      }
    }
    for (PinRPA *pin : row[indexOther]->l2r_) {
      for (AccessPoint ap : pin->ap_list_) {
        ap.x -= deltaOther;
      }
    }
  }
  // std::swap(row[indexA], row[indexB]);
  swap_cell = row[indexA];
  row[indexA] = row[indexB];
  row[indexB] = swap_cell;
}

void
Opendp::rpaSwapIncrement(int row_index, int indexA, int indexB,
                        vector<Move *> moves, int dint, int isReport)
{
  bool compute_together = false;
  if (std::abs(indexA - indexB) < 3)
    compute_together = true;

  float delta1 = 0, delta2 = 0;

  // Swap two cells
  CellRPA *swap_cell = cellrpas_row_[row_index][indexA];
  cellrpas_row_[row_index][indexA] = cellrpas_row_[row_index][indexB];
  cellrpas_row_[row_index][indexB] = swap_cell;

  int index_main = indexB;
  int index_other = indexA;

  // Update the location of other cell
  int other_llx = cellrpas_row_[row_index][index_other]->llx_;
  int main_llx = cellrpas_row_[row_index][index_main]->llx_;
  bool main_is_flipped = cellrpas_row_[row_index][index_main]->is_flipped_;
  cellrpas_row_[row_index][index_other]->llx_ = main_llx;

  if (!compute_together) {
    float init_ioc = 0;
    for (int i = index_other - 1; i >= 0 & i <= index_other; i++) {
      init_ioc += cellrpas_row_[row_index][i]->ioc_;
    }
    int start_index = index_other - 1 >= 0 ? index_other - 1 : index_other;
    int end_index = index_other + 1 <
        cellrpas_row_[row_index].size() ? index_other + 1 : index_other;
    float final_ioc = rpaIncrementHelp(start_index, end_index,
                                      row_index, dint, isReport);
    delta1 = init_ioc - final_ioc;
  }
  int start_index, end_index;
  if (compute_together) {
    int hindex = index_main > index_other ? index_main : index_other;
    int lindex = index_main > index_other ? index_other : index_main;
    start_index = lindex - 1 >= 0 ? lindex - 1 : lindex;
    end_index = hindex + 1 < cellrpas_row_[row_index].size() ?
                hindex + 1 : hindex;
  } else {
    start_index = index_main - 1 >= 0 ? index_main - 1 : index_main;
    end_index = index_main + 1 < cellrpas_row_[row_index].size() ?
                index_main + 1 : index_main;
  }

  float init_ioc = 0;
  for (int i = start_index; i <= end_index; i++) {
    init_ioc += cellrpas_row_[row_index][i]->ioc_;
  }

  for (Move *move : moves) {
    cellrpas_row_[row_index][index_main]->llx_ = move->movement - core_.xMin();
    cellrpas_row_[row_index][index_main]->is_flipped_ = move->flip != main_is_flipped ?
                                                        true : false;
    float final_ioc = rpaIncrementHelp(start_index, end_index, row_index, dint, isReport);
    delta2 = init_ioc - final_ioc;
    move->delta = delta2 + delta1;
  }

  // Update back the cells
  cellrpas_row_[row_index][index_main]->llx_ = main_llx;
  cellrpas_row_[row_index][index_main]->is_flipped_ = main_is_flipped;
  cellrpas_row_[row_index][index_other]->llx_ = other_llx;
  swap_cell = cellrpas_row_[row_index][indexA];
  cellrpas_row_[row_index][indexA] = cellrpas_row_[row_index][indexB];
  cellrpas_row_[row_index][indexB] = swap_cell;
}

// default dint is 2000
void
Opendp::RPAGenerate(int dint, vector<vector<Cell_RPA *>> &cell_rpas)
{
  // cell_rpas_
  // RPA Computation starts
  for (int i = 0; i < cell_rpas.size(); i++) {
    for (int j = 0; j < cell_rpas[i].size(); j++) {
      for (int k = 0; k < cell_rpas[i][j]->pins.size(); k++) {
        double xPinRPA = cell_rpas[i][j]->pins[k].xAPs.size();
        double yPinRPA = cell_rpas[i][j]->pins[k].yAPs.size();
        if ((xPinRPA == 0) & (yPinRPA == 0)) {
          cell_rpas[i][j]->rpa = std::min(cell_rpas[i][j]->rpa, -2.0);
        }
        string pinName = cell_rpas[i][j]->pins[k].mpin->getMTerm()->getName();
        string cellName = cell_rpas[i][j]->db_inst_->getName();
        logger_->report("Cell:{:s} Pin:{:s}", cellName, pinName);
        for (AccessPoint APmain : cell_rpas[i][j]->pins[k].xAPs) {
          for (int l = 1; l < 4; l++) {
            //check left neighbors
            if ((k - l) < 0) {
              if ((j - 1) >= 0) {
                int size = cell_rpas[i][j - 1]->pins.size();
                double rpaTrack = 0;
                if ((size + (k - l)) >= 0) {
                  for (AccessPoint APneib : cell_rpas[i][j - 1]->pins[size + (k - l)].xAPs) {
                    if ((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer)) {
                      rpaTrack += 1;
                    }
                  }
                  if (cell_rpas[i][j - 1]->pins[size + (k - l)].xAPs.size() != 0) {
                    double upa = rpaTrack / cell_rpas[i][j - 1]->pins[size + (k - l)].xAPs.size();
                    xPinRPA = xPinRPA - upa;
                    logger_->report("UAP: {:f}", upa);
                  }
                }
              }
            }
            //neighbor is inside main cell
            else {
              double rpaTrack = 0;
              for (AccessPoint APneib : cell_rpas[i][j]->pins[k - l].xAPs) {
                if ((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer)) {
                  rpaTrack += 1;
                }
              }
              if (cell_rpas[i][j]->pins[k - l].xAPs.size() != 0) {
                double upa = rpaTrack / cell_rpas[i][j]->pins[k - l].xAPs.size();
                xPinRPA = xPinRPA - upa;
                logger_->report("UAP: {:f}", upa);
              }
            }
            // check right nerghbors
            // right neighbor is not in main cell
            if ((k + l) >= cell_rpas[i][j]->pins.size()) {
              if ((j + 1) < cell_rpas[i].size()) {
                // int size = cell_rpas[i][j+1]->pins.size();
                double rpaTrack = 0;
                int index = k + l - cell_rpas[i][j]->pins.size();
                if (index < cell_rpas[i][j + 1]->pins.size()) {
                  for (AccessPoint APneib : cell_rpas[i][j + 1]->pins[index].xAPs) {
                    if ((std::abs(APmain.x - APneib.x) <= dint) &
                        (APmain.y == APneib.y) & (APmain.layer == APneib.layer)) {
                      rpaTrack += 1;
                    }
                  }
                  if (cell_rpas[i][j + 1]->pins[index].xAPs.size() != 0) {
                    double upa = rpaTrack / cell_rpas[i][j + 1]->pins[index].xAPs.size();
                    xPinRPA = xPinRPA - upa;
                    logger_->report("UAP: {:f}", upa);
                  }
                }
              }
            } else {
              // neighbor is inside main cell
              double rpaTrack = 0;
              for (AccessPoint APneib : cell_rpas[i][j]->pins[k + l].xAPs) {
                if ((std::abs(APmain.x - APneib.x) <= dint) &
                    (APmain.y == APneib.y) & (APmain.layer == APneib.layer)) {
                  rpaTrack += 1;
                }
              }
              if (cell_rpas[i][j]->pins[k + l].xAPs.size() != 0) {
                double upa = rpaTrack / cell_rpas[i][j]->pins[k + l].xAPs.size();
                xPinRPA = xPinRPA - upa;
                logger_->report("UAP: {:f}", upa);
              }
            }
          }
        }
        xPinRPA -= 1;
        yPinRPA -= 1;
        logger_->report("Cell:{:s} Pin:{:s} RPA:{:f}", cellName, pinName, xPinRPA);
        // double minPinRPA = xPinRPA < yPinRPA?xPinRPA:yPinRPA;
        cell_rpas[i][j]->rpa += xPinRPA < 0 ? xPinRPA : 0;
      }
    }
  }
}

void
Opendp::detailedPlacement(int max_displacement_x,
                          int max_displacement_y)
{
  //int dbUnit = block_->getDefUnits();
  importDb();
  float dbUnit = db_->getChip()->getBlock()->getDefUnits();
  if (max_displacement_x == 0 || max_displacement_y == 0) {
    // defaults
    max_displacement_x_ = 500;
    max_displacement_y_ = 100;
  } else {
    max_displacement_x_ = max_displacement_x;
    max_displacement_y_ = max_displacement_y;
  }

  reportImportWarnings();
  hpwl_before_ = hpwl();
  detailedPlacement();
  // Save displacement stats before updating instance DB locations.
  findDisplacementStats();
  updateDbInstLocations();

  if (!placement_failures_.empty()) {
    logger_->info(DPL, 34, "Detailed placement failed on:");
    for (auto inst : placement_failures_)
      logger_->info(DPL, 35, " {}", inst->getName());
    logger_->error(DPL, 36, "Detailed placement failed.");
  }
  //}
}

void
Opendp::updateDbInstLocations()
{
  for (Cell &cell : cells_) {
    if (!isFixed(&cell) && isStdCell(&cell)) {
      dbInst *db_inst_ = cell.db_inst_;
      // Only move the instance if necessary to avoid triggering callbacks.
      if (db_inst_->getOrient() != cell.orient_)
        db_inst_->setOrient(cell.orient_);
      int x = core_.xMin() + cell.x_;
      int y = core_.yMin() + cell.y_;
      int inst_x, inst_y;
      db_inst_->getLocation(inst_x, inst_y);
      if (x != inst_x || y != inst_y)
        db_inst_->setLocation(x, y);
    }
  }
}

void
Opendp::reportLegalizationStats() const
{
  logger_->report("Placement Analysis");
  logger_->report("---------------------------------");
  logger_->report("total displacement   {:10.1f} u", dbuToMicrons(displacement_sum_));
  logger_->report("average displacement {:10.1f} u", dbuToMicrons(displacement_avg_));
  logger_->report("max displacement     {:10.1f} u", dbuToMicrons(displacement_max_));
  logger_->report("original HPWL        {:10.1f} u", dbuToMicrons(hpwl_before_));
  double hpwl_legal = hpwl();
  logger_->report("legalized HPWL       {:10.1f} u", dbuToMicrons(hpwl_legal));
  int hpwl_delta = (hpwl_before_ == 0.0)
      ? 0.0
      : round((hpwl_legal - hpwl_before_) / hpwl_before_ * 100);
  logger_->report("delta HPWL           {:10} %", hpwl_delta);
  logger_->report("");
}

////////////////////////////////////////////////////////////////

/////////////////////// DP Improver ////////////////////////////
static bool
comparator1(const Cell lhs, const Cell rhs)
{
  return lhs.y_ < rhs.y_;
}

static bool
comparator2(const Cell *lhs, const Cell *rhs)
{
  return lhs->x_ < rhs->x_;
}

bool
Opendp::checkSwap(int i, int j, vector<Cell *> row)
{
  if (row[i]->hold_ || row[j]->hold_ || isFixed(row[i]) || isFixed(row[j])) {
    // logger_->report("Inside checkSwap");
    return false;
  }

  int check1 = 10;
  int check2 = 10;

  if (i + 1 < row.size()) {
    check1 = (row[i + 1]->x_ - padLeft(row[i]) * site_width_ * 2 -
              (row[i]->x_ + row[j]->width_)) / site_width_;
  }

  if (j + 1 < row.size()) {
    check2 = (row[j + 1]->x_ - padLeft(row[j]) * site_width_ * 2 -
              (row[j]->x_ + row[i]->width_)) / site_width_;
  }

  if (check1 < 0 || check2 < 0) {
    // if(i == j)
    // printf("they are the same!!!!");
    return false;
  }
  return true;
}

// Computes HPWL change of a net based on the new horizontal
// location of the cell and the flipping condition.
// This function is used in mirror OPT.
int64_t
Opendp::hpwl_increment(dbInst *inst, vector<dbITerm *> iterms,
                        dbNet *net, int pt_x, bool mirror) const
{
  Rect netBox = getBox(net);
  int64_t net_hpwl = netBox.dx() + netBox.dy();
  Rect iterm_box;
  iterm_box.mergeInit();
  int cellPtX, cellPtY;
  inst->getLocation(cellPtX, cellPtY);
  int cellWidth = inst->getMaster()->getWidth();

  for (int i = 0; i < iterms.size(); i++) {
    dbITerm *iterm = iterms[i];
    int x, y;
    if (iterm->getAvgXY(&x, &y)) {
      Rect iterm_rect(x, y, x, y);
      iterm_box.merge(iterm_rect);
    } else {
      // This clause is sort of worthless because getAvgXY prints
      // a warning when it fails.
      dbInst *inst = iterm->getInst();
      dbBox *inst_box = inst->getBBox();
      int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
      int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
      Rect iterm_rect(center_x, center_y, center_x, center_y);
      iterm_box.merge(iterm_rect);
    }
  }

  // Based on current location check the pin location in the netbox
  bool isInside = netBox.inside(iterm_box);

  // Calculate the new pin delta displacement
  int mirror_x = 0;
  if (mirror) {
    mirror_x = 2 * cellPtX + cellWidth - iterm_box.xMin() - iterm_box.xMax();
  }

  int delta_x = pt_x - cellPtX + mirror_x;

  // Considering there wont be any movement along the y axis
  iterm_box.moveDelta(delta_x, 0);
  bool isContain = netBox.contains(iterm_box);

  // Pin term is inside the net box before and after movement.
  if (isInside && isContain) {
    return 0;
  }

  // Pin term is initially inside the net box but after movement is outside the netbox
  if (isInside) {
    netBox.merge(iterm_box);
    int64_t new_hpwl = netBox.dx() + netBox.dy();
    return new_hpwl - net_hpwl;
  }

  // Re calculate the Net box with the updated iterm location
  Rect new_net_box;
  new_net_box.mergeInit();

  for (dbITerm *iterm_ : net->getITerms()) {
    int i = std::find(iterms.begin(), iterms.end(), iterm_) - iterms.begin();
    if (i >= iterms.size()) {
      int x, y;
      if (iterm_->getAvgXY(&x, &y)) {
        Rect iterm_rect_(x, y, x, y);
        new_net_box.merge(iterm_rect_);
      } else {
        // This clause is sort of worthless because getAvgXY prints
        // a warning when it fails.
        dbInst *inst = iterm_->getInst();
        dbBox *inst_box = inst->getBBox();
        int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
        int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
        Rect inst_center(center_x, center_y, center_x, center_y);
        new_net_box.merge(inst_center);
      }
    }
  }
  new_net_box.merge(iterm_box);
  for (dbBTerm *bterm : net->getBTerms()) {
    for (dbBPin *bpin : bterm->getBPins()) {
      dbPlacementStatus status = bpin->getPlacementStatus();
      if (status.isPlaced()) {
        Rect pin_bbox = bpin->getBBox();
        int center_x = (pin_bbox.xMin() + pin_bbox.xMax()) / 2;
        int center_y = (pin_bbox.yMin() + pin_bbox.yMax()) / 2;
        Rect pin_center(center_x, center_y, center_x, center_y);
        new_net_box.merge(pin_center);
      }
    }
  }
  int64_t new_hpwl = new_net_box.dx() + new_net_box.dy();
  // return net_hpwl - new_hpwl;
  return new_hpwl - net_hpwl;
}

// Compute HPWL change due to the horizontal movement of a cell
// and its orientation change. This function is used in mirror OPT.
int64_t
Opendp::hpwl_increment(dbInst *inst, int pt_x, bool mirror) const
{
  int64_t delta = 0;
  // get an array of all the nets connects to the cell without duplication using array of pins)
  vector<dbNet *> nets;
  vector<vector<dbITerm *>> iterms;

  for (dbITerm *iterm : inst->getITerms()) {
    if (iterm->getNet() != NULL) {
      dbNet *net = iterm->getNet();

      int i = std::find(nets.begin(), nets.end(), net) - nets.begin();

      if (i >= nets.size()) {
        nets.push_back(net);
        vector<dbITerm *> newvector;
        newvector.push_back(iterm);
        iterms.push_back(newvector);
      } else {
        iterms[i].push_back(iterm);
      }
    }
  }

  for (int i = 0; i < nets.size(); i++) {
    dbNet *net = nets[i];
    if (isSupply(net) == false) {
      delta = delta + hpwl_increment(inst, iterms[i], net, pt_x, mirror);
    }
  }
  return delta;
}

// Compute HPWL change for multiple move of a cell.
// This is used to find optimal shifting point.
void
Opendp::hpwl_increment(dbInst *inst, vector<Move *> moves)
{
  // get an array of all the nets connects to the cell without duplication using array of pins
  vector<dbNet *> nets;
  vector<vector<dbITerm *>> iterms;

  for (dbITerm *iterm : inst->getITerms()) {
    dbNet *net = iterm->getNet();

    int i = std::find(nets.begin(), nets.end(), net) - nets.begin();

    if (i >= nets.size()) {
      nets.push_back(net);
      vector<dbITerm *> newvector;
      newvector.push_back(iterm);
      iterms.push_back(newvector);
    } else {
      iterms[i].push_back(iterm);
    }
  }

  for (int i = 0; i < nets.size(); i++) {
    dbNet *net = nets[i];
    if (net != nullptr) {
      if (isSupply(net) == false) {
        hpwl_increment(inst, iterms[i], net, moves);
      }
    }
  }
}

bool
Opendp::checkValid(int origincell, int swapcell, int shift, vector<Cell *> row)
{
  int check1 = 10;
  int check2 = 10;
  if (swapcell + 1 < row.size()) {
    check1 = (row[swapcell + 1]->x_ - (row[swapcell]->x_ +
              row[origincell]->width_) -
              padLeft(row[swapcell]) * site_width_ * 2
              - shift * site_width_) / site_width_;
  } else {
    if ((row[swapcell]->x_ + row[origincell]->width_ + shift * site_width_) >
        (row[swapcell]->x_ + row[swapcell]->width_)) {
      return false;
    }
  }
  if ((swapcell - 1) != origincell) {
    if (swapcell - 1 >= 0) {
      check2 = (row[swapcell]->x_ - (row[swapcell - 1]->x_ +
                row[swapcell - 1]->width_) -
                padLeft(row[swapcell]) * site_width_ * 2 +
                shift * site_width_) / site_width_;
    }
  } else {
    check2 = (row[swapcell]->x_ - (row[swapcell - 1]->x_ +
              row[swapcell]->width_) -
              padLeft(row[swapcell]) * site_width_ * 2 +
              shift * site_width_) / site_width_;
  }
  if (check1 < 0 || check2 < 0 || check1 == 1 || check2 == 1) {
    return false;
  }
  if ((row[swapcell]->x_ + shift * site_width_) < 0) {
    return false;
  }
  // printf("check 1 is %d and check 2 is %d\n", check1, check2);
  return true;
}

// Compute HPWL change for multiple move of a cell.
// This is used to find optimal shifting point.
void
Opendp::hpwl_increment(dbInst *inst, vector<dbITerm *> iterms,
                        dbNet *net, vector<Move *> moves)
{
  Rect netBox = getBox(net);
  int64_t net_hpwl = netBox.dx() + netBox.dy();
  Rect iterm_box;
  iterm_box.mergeInit();
  int cellPtX, cellPtY;
  inst->getLocation(cellPtX, cellPtY);
  int cellWidth = inst->getMaster()->getWidth();

  for (int i = 0; i < iterms.size(); i++) {
    dbITerm *iterm = iterms[i];
    int x, y;
    if (iterm->getAvgXY(&x, &y)) {
      Rect iterm_rect(x, y, x, y);
      iterm_box.merge(iterm_rect);
    } else {
      // This clause is sort of worthless because getAvgXY prints
      // a warning when it fails.
      dbInst *inst = iterm->getInst();
      dbBox *inst_box = inst->getBBox();
      int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
      int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
      Rect iterm_rect(center_x, center_y, center_x, center_y);
      iterm_box.merge(iterm_rect);
    }
  }

  // Based on current location check the pin location in the netbox
  bool isInside = netBox.inside(iterm_box);

  for (Move *movesm : moves) {
    // Calculate the new pin delta displacement
    int mirror_x = 0;
    if (movesm->flip) {
      mirror_x = 2 * cellPtX + cellWidth - iterm_box.xMin() - iterm_box.xMax();
    }
    int delta_x = movesm->movement - cellPtX + mirror_x;

    // Considering there wont be any movement along the y axis
    iterm_box.moveDelta(delta_x, 0);
    bool isContain = netBox.contains(iterm_box);

    // Pin term is inside the net box before and after movement.
    if (isInside && isContain) {
      iterm_box.moveDelta(-delta_x, 0);
      continue;
    }
    // Pin term is initially inside the net box but after movement is outside the netbox
    if (isInside) {
      Rect temp;
      netBox.merge(iterm_box, temp);
      int64_t new_hpwl = temp.dx() + temp.dy();
      movesm->delta += (new_hpwl - net_hpwl);
      iterm_box.moveDelta(-delta_x, 0);
      continue;
    }

    // Re calculate the Net box with the updated iterm location
    Rect new_net_box;
    new_net_box.mergeInit();

    for (dbITerm *iterm_ : net->getITerms()) {
      int i = std::find(iterms.begin(), iterms.end(), iterm_) - iterms.begin();
      if (i >= iterms.size()) {
        int x, y;
        if (iterm_->getAvgXY(&x, &y)) {
          Rect iterm_rect_(x, y, x, y);
          new_net_box.merge(iterm_rect_);
        } else {
          // This clause is sort of worthless because getAvgXY prints
          // a warning when it fails.
          dbInst *inst = iterm_->getInst();
          dbBox *inst_box = inst->getBBox();
          int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
          int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
          Rect inst_center(center_x, center_y, center_x, center_y);
          new_net_box.merge(inst_center);
        }
      }
    }
    new_net_box.merge(iterm_box);
    for (dbBTerm *bterm : net->getBTerms()) {
      for (dbBPin *bpin : bterm->getBPins()) {
        dbPlacementStatus status = bpin->getPlacementStatus();
        if (status.isPlaced()) {
          Rect pin_bbox = bpin->getBBox();
          int center_x = (pin_bbox.xMin() + pin_bbox.xMax()) / 2;
          int center_y = (pin_bbox.yMin() + pin_bbox.yMax()) / 2;
          Rect pin_center(center_x, center_y, center_x, center_y);
          new_net_box.merge(pin_center);
        }
      }
    }
    int64_t new_hpwl = new_net_box.dx() + new_net_box.dy();
    // return net_hpwl - new_hpwl;
    movesm->delta += (new_hpwl - net_hpwl);
    iterm_box.moveDelta(-delta_x, 0);
  }
}

void
Opendp::hpwl_increment(dbInst *inst, vector<Move *> moves, vector<dbInst *> others,
                        vector<Move *> movess)
{
  // get an array of all the nets connects to the cell without duplication using array of pins)
  vector<dbNet *> nets;
  vector<vector<dbITerm *>> iterms;
  for (dbITerm *iterm : inst->getITerms()) {
    dbNet *net = iterm->getNet();

    int i = std::find(nets.begin(), nets.end(), net) - nets.begin();

    if (i >= nets.size()) {
      nets.push_back(net);
      vector<dbITerm *> newvector;
      newvector.push_back(iterm);
      iterms.push_back(newvector);
    } else {
      iterms[i].push_back(iterm);
    }
  }

  vector<vector<vector<dbITerm *>>> itermsss;
  // inst's net's iterms

  for (int j = 0; j < others.size(); j++) {
    vector<vector<dbITerm *>> itermss;
    for (dbITerm *iterm : others[j]->getITerms()) {
      dbNet *net = iterm->getNet();

      int i = std::find(nets.begin(), nets.end(), net) - nets.begin();

      if (i >= nets.size()) {
        nets.push_back(net);
        while (itermss.size() <= i) {
          vector<dbITerm *> newvector;
          itermss.push_back(newvector);
        }
        itermss[i].push_back(iterm);
      } else {
        while (itermss.size() <= i) {
          vector<dbITerm *> newvector;
          itermss.push_back(newvector);
        }
        itermss[i].push_back(iterm);
      }
    }
    itermsss.push_back(itermss);
  }

  while (iterms.size() < nets.size()) {
    vector<dbITerm *> newvector;
    iterms.push_back(newvector);
  }

  for (int i = 0; i < nets.size(); i++) {
    dbNet *net = nets[i];
    if (net != nullptr) {
      if (isSupply(net) == false) {
        int netCount = i;
        hpwl_increment(inst, iterms[i], net, moves, itermsss, others, movess, netCount);
      }
    }
  }
}

// Delta HPWL calculation for multiple cells are moving together
void
Opendp::hpwl_increment(dbInst *inst, vector<dbITerm *> iterms, dbNet *net,
                        vector<Move *> moves, vector<vector<vector<dbITerm *>>> itermss,
                        vector<dbInst *> others, vector<Move *> movess, int netCount)
{
  // printf("others size is %d and itermss size is %d\n",others.size(),itermss.size());
  Rect netBox = getBox(net);
  int64_t net_hpwl = netBox.dx() + netBox.dy();
  // Main instance term box
  Rect iterm_box;
  iterm_box.mergeInit();
  int cellPtX, cellPtY;
  inst->getLocation(cellPtX, cellPtY);
  int cellWidth = inst->getMaster()->getWidth();

  if (iterms.size() == 0) {
    iterm_box.set_xlo(-10);
  }

  // for the main cell
  for (int i = 0; i < iterms.size(); i++) {
    dbITerm *iterm = iterms[i];
    int x, y;
    if (iterm->getAvgXY(&x, &y)) {
      Rect iterm_rect(x, y, x, y);
      iterm_box.merge(iterm_rect);
    } else {
      // This clause is sort of worthless because getAvgXY prints
      // a warning when it fails.
      dbInst *inst = iterm->getInst();
      dbBox *inst_box = inst->getBBox();
      int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
      int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
      Rect iterm_rect(center_x, center_y, center_x, center_y);
      iterm_box.merge(iterm_rect);
    }
  }

  // ith Other instances' termp_boxes
  vector<Rect> iterm_boxs;
  // for other cells
  for (int j = 0; j < itermss.size(); j++) {
    Rect temp;
    temp.mergeInit();
    if (itermss[j].size() <= netCount) {
      temp.set_xlo(-10);
      iterm_boxs.push_back(temp);
      continue;
    } else {
      if (itermss[j][netCount].size() == 0) {
        temp.set_xlo(-10);
        iterm_boxs.push_back(temp);
        continue;
      }
    }
    for (int i = 0; i < itermss[j][netCount].size(); i++) {
      dbITerm *iterm = itermss[j][netCount][i];
      int x, y;
      if (iterm->getAvgXY(&x, &y)) {
        Rect iterm_rect(x, y, x, y);
        temp.merge(iterm_rect);
      } else {
        // This clause is sort of worthless because getAvgXY prints
        // a warning when it fails.
        dbInst *inst = iterm->getInst();
        dbBox *inst_box = inst->getBBox();
        int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
        int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
        Rect iterm_rect(center_x, center_y, center_x, center_y);
        temp.merge(iterm_rect);
      }
    }
    iterm_boxs.push_back(temp);
  }

  // Based on current location check the pin location in the netbox
  Rect temp;
  temp.mergeInit();
  if (iterm_box.xMin() != -10) {
    temp.merge(iterm_box);
  }

  // merge all pins
  for (int j = 0; j < iterm_boxs.size(); j++) {
    if (iterm_boxs[j].xMin() != -10) {
      temp.merge(iterm_boxs[j]);
    }
  }
  bool isInside = netBox.inside(temp);

  // Contain the box of terms of other instances connected with the net
  Rect tempp;
  tempp.mergeInit();

  for (int j = 0; j < iterm_boxs.size(); j++) {
    if (iterm_boxs[j].xMin() != -10) {
      int cellPtXX, cellPtYY;
      others[j]->getLocation(cellPtXX, cellPtYY);
      // Any reason for not considering the mirroring part?
      int delta_xx = movess[j]->movement - cellPtXX;
      // Considering there wont be any movement along the y axis
      iterm_boxs[j].moveDelta(delta_xx, 0);
      tempp.merge(iterm_boxs[j]);
    }
  }

  // Contain the box of terms of other instances connected with tempp
  Rect keep;
  keep.mergeInit();
  keep.merge(tempp);
  for (Move *movesm : moves) {
    // Calculate the new pin delta displacement
    int delta_x = 0;
    if (iterm_box.xMin() != -10) {
      int mirror_x = 0;
      if (movesm->flip) {
        mirror_x = 2 * cellPtX + cellWidth - iterm_box.xMin() - iterm_box.xMax();
      }
      delta_x = movesm->movement - cellPtX + mirror_x;
      // Considering there wont be any movement along the y axis
      iterm_box.moveDelta(delta_x, 0);
      tempp.merge(iterm_box);
    }
    // for other cells movement

    bool isContain = netBox.contains(tempp);

    // Pin term is inside the net box before and after movement.
    if (isInside && isContain) {
      iterm_box.moveDelta(-delta_x, 0);
      tempp.mergeInit();
      tempp.merge(keep);
      continue;
    }
    // Pin term is initially inside the net box but after movement is outside the netbox
    if (isInside) {
      Rect temp;
      temp.mergeInit();
      netBox.merge(tempp, temp);
      int64_t new_hpwl = temp.dx() + temp.dy();
      movesm->delta += (new_hpwl - net_hpwl);
      iterm_box.moveDelta(-delta_x, 0);
      tempp.mergeInit();
      tempp.merge(keep);
      continue;
    }

    // Re calculate the Net box with the updated iterm location
    Rect new_net_box;
    new_net_box.mergeInit();
    bool check = false;
    for (dbITerm *iterm_ : net->getITerms()) {
      check = false;
      int i = std::find(iterms.begin(), iterms.end(), iterm_) - iterms.begin();
      if (i >= iterms.size()) {
        // for other cell box
        for (int j = 0; j < iterm_boxs.size(); j++) {
          if (itermss[j].size() <= netCount) {
            continue;
          }
          i = std::find(itermss[j][netCount].begin(), itermss[j][netCount].end(), iterm_) -
            itermss[j][netCount].begin();
          if (i < itermss[j][netCount].size()) {
            check = true;
            break;
          }
        }
      } else {
        check = true;
      }
      if (!check) {
        int x, y;
        if (iterm_->getAvgXY(&x, &y)) {
          Rect iterm_rect_(x, y, x, y);
          new_net_box.merge(iterm_rect_);
        } else {
          // This clause is sort of worthless because getAvgXY prints
          // a warning when it fails.
          dbInst *inst = iterm_->getInst();
          dbBox *inst_box = inst->getBBox();
          int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
          int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
          Rect inst_center(center_x, center_y, center_x, center_y);
          new_net_box.merge(inst_center);
        }
      }
    }

    if (iterm_box.xMin() != -10) {
      new_net_box.merge(iterm_box);
    }
    new_net_box.merge(keep);

    for (dbBTerm *bterm : net->getBTerms()) {
      for (dbBPin *bpin : bterm->getBPins()) {
        dbPlacementStatus status = bpin->getPlacementStatus();
        if (status.isPlaced()) {
          Rect pin_bbox = bpin->getBBox();
          int center_x = (pin_bbox.xMin() + pin_bbox.xMax()) / 2;
          int center_y = (pin_bbox.yMin() + pin_bbox.yMax()) / 2;
          Rect pin_center(center_x, center_y, center_x, center_y);
          new_net_box.merge(pin_center);
        }
      }
    }
    int64_t new_hpwl = new_net_box.dx() + new_net_box.dy();
    movesm->delta += (new_hpwl - net_hpwl);
    iterm_box.moveDelta(-delta_x, 0);
    tempp.mergeInit();
    tempp.merge(keep);
  }
}

bool
Opendp::swapCellss(Cell *cell1, Cell *cell2)
{
  if (cell1 != cell2 && !cell1->hold_ && !cell2->hold_ &&
      !isFixed(cell1) && !isFixed(cell2)) {
    if (cell2->x_ > cell1->x_) {
      int temp = cell2->x_ + cell2->width_ - cell1->width_ -
                  padLeft(cell1) * site_width_;
      int grid_x1 = temp / site_width_;
      int grid_y1 = gridY(cell2);
      int grid_x2 = gridPaddedX(cell1);
      int grid_y2 = gridY(cell1);
      erasePixel(cell1);
      erasePixel(cell2);
      paintPixel(cell2, grid_x2, grid_y2);
      paintPixel(cell1, grid_x1, grid_y1);
    } else {
      int temp = cell1->x_ + cell1->width_ - cell2->width_ -
                  padLeft(cell1) * site_width_;
      int grid_x2 = (temp) / site_width_;
      int grid_y2 = gridY(cell1);
      int grid_x1 = gridPaddedX(cell2);
      int grid_y1 = gridY(cell2);
      erasePixel(cell1);
      erasePixel(cell2);
      paintPixel(cell1, grid_x1, grid_y1);
      paintPixel(cell2, grid_x2, grid_y2);
    }
    return true;
  }
  return false;
}

void
Opendp::updateRow(vector<vector<Cell *>> &all, vector<Cell> &tmpCells_,
                  vector<dpRow *> &sortedRows)
{
  // sort(tmpCells_.begin(), tmpCells_.end(), &comparator1);
  int cellCount = <int>tmpCells_.size();

  int i = 0;

  int rowSize = sortedRows.size();
  // logger_->report("Probelm is in the sort funciton");
  // sort(sortedRows.begin(), sortedRows.end(), &comparator3);
  // logger_->report("Probelm is not in the sort funciton");

  vector<Cell *> row;
  int j = 0;
  int db_row_miny = sortedRows[j]->y_;
  int db_row_maxx = sortedRows[j]->x_;
  j++;

  i = 0;
  Cell *temp = &tmpCells_[i];
  i++;

  // logger_->report("Cell Master name {:s}\n", master->getName());
  // logger_->report("Cell count:{:d} and Row Count:{:d}", cellCount, rowSize);
  while (i <= cellCount && j <= rowSize) {
    if (db_row_miny != temp->y_ || i == cellCount) {
      if (db_row_miny == temp->y_ && i == cellCount) {
        row.push_back(temp);
      } else if (db_row_miny != temp->y_ && i == cellCount) {
        row.clear();
        row.push_back(temp);
        all.push_back(row);
        break;
      }
      sort(row.begin(), row.end(), &comparator2);
      vector<Cell *> tmprow;
      int rowLength = row.size();
      int k = 0;
      while (k <= rowLength) {
        if (k < rowLength && row[k]->x_ < db_row_maxx) {
          tmprow.push_back(row[k]);
          k++;
        } else {
          // logger_->report("Row is added in all");
          all.push_back(tmprow);
          tmprow.clear();

          // || db_row_miny != row[k-1]->y_
          if (k == rowLength || j == rowSize) {
            // logger_->report("Test that it breaks from row");
            break;
          }
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
      }

      row.clear();
      while (db_row_miny != temp->y_ && i < cellCount && j < rowSize) {
        while (db_row_miny < temp->y_) {
          db_row_miny = sortedRows[j]->y_;
          db_row_maxx = sortedRows[j]->x_;
          j++;
        }
        while (temp->y_ < db_row_miny) {
          dbMaster *tmpMaster = temp->db_inst_->getMaster();
          logger_->report("Row Y and Cell Y not Matching: Cell Master Name:{:s}",
                          tmpMaster->getName());
          temp = &tmpCells_[i];
          i++;
        }
      }
      if (i == cellCount) {
        // logger_->report("Breaks from ponint 1");
        break;
      }
      // logger_->report("Current Row Y:{:d} Cell Y:{:d}",db_row_miny,temp->y_);
    }
    row.push_back(temp);
    temp = &tmpCells_[i];
    i++;
  }
  while (j == rowSize && i < cellCount) {
    temp = &tmpCells_[i];
    dbMaster *tmpMaster = temp->db_inst_->getMaster();
    logger_->report("Cells not able to find any valid row Cell:{:s} X:{:d} Y:{:d}",
                    tmpMaster->getName(),
                    temp->x_,
                    temp->y_);
    i++;
  }
  // logger_->report("Update Row is Finished");
}

void
Opendp::RPATest()
{
  // Get def detials
  // float dbUnit = 1.0*(block_->getDefUnits());
  // char s1 = '{', s2 = '}';
  improver(10, 10, 1);
  return;
  // Initialize opendp
  importDb();
  initGrid();

  // Paint fixed cells.
  setFixedGridCells();

  auto comparatorLambda2 = [](const CellRPA lhs, const CellRPA rhs) {
    return lhs.lly_ < rhs.lly_;
  };

  sort(cellrpas_.begin(), cellrpas_.end(), comparatorLambda2);

  odb::dbSet<dbRow> rows = block_->getRows();
  vector<dpRow *> sortedRows;
  int maxRowY = INT_MIN;
  int minRowY = INT_MAX;

  for (dbRow *row : rows) {
    Rect rowBox;
    row->getBBox(rowBox);
    int y_ = rowBox.yMin();
    int x_ = rowBox.xMax();
    x_ -= core_.xMin();
    y_ -= core_.yMin();
    if (y_ > maxRowY)
      maxRowY = y_;
    if (y_ < minRowY)
      minRowY = y_;
    dpRow *tmprow = new dpRow(x_, y_);
    sortedRows.push_back(tmprow);
  }

  sort(sortedRows.begin(), sortedRows.end(), &comparator3);
  updateRow(cellrpas_row_, cellrpas_, sortedRows);

  GenerateAP(420);
  ComputeRPA(420, cellrpas_row_);
  /*
  for ( int i = 0; i < cell_rpas.size(); i++) {
    for ( int j = 0; j < cell_rpas[i].size(); j++) {
      string cellName = cell_rpas[i][j]->db_inst_->getName();
      float x = (cell_rpas[i][j]->llx_)/dbUnit;
      float y = (cell_rpas[i][j]->lly_)/dbUnit;
      logger_->report("Cell:{:s} X:{:f} Y:{:f}", cellName, x, y);
    }
  }
  */

  for (CellRPA &tmpCell : cellrpas_) {
    string cellName = tmpCell.db_inst_->getName();
    dbMaster *master = tmpCell.db_inst_->getMaster();
    string cellMasterName = master->getName();
    logger_->report("Cell:{:s} Master:{:s} IOC:{:f}", cellName, cellMasterName, tmpCell.ioc_);

    for (PinRPA *tmpPin : tmpCell.l2r_) {
      string pin_name = tmpPin->mterm_->getName();
      logger_->report("PIN:{:s} RPA:{:f} Boundary:{:d}", pin_name, tmpPin->actual_rpa_value_, tmpPin->is_boundary_);
    }
  }
}

void
Opendp::improver(int swaprange, int shiftrange, int iter)
{
  importDb();
  initGrid();
  // Paint fixed cells.
  setFixedGridCells();
  double hpwl_actual = hpwl();
  // SwapAndShift(40,5);
  std::chrono::time_point<std::chrono::system_clock> start, end;

  start = std::chrono::system_clock::now();
  // SwapAndShift(0,0);
  // swap();
  vector<Cell> tmpCells_(cells_);
  sort(tmpCells_.begin(), tmpCells_.end(), &comparator1);

  map<int, int> id2index;

  odb::dbSet<dbRow> rows = block_->getRows();
  vector<dpRow *> sortedRows;
  int maxRowY = INT_MIN;
  int minRowY = INT_MAX;
  for (dbRow *row : rows) {
    Rect rowBox;
    row->getBBox(rowBox);
    int y_ = rowBox.yMin();
    int x_ = rowBox.xMax();
    x_ -= core_.xMin();
    y_ -= core_.yMin();
    if (y_ > maxRowY)
      maxRowY = y_;
    if (y_ < minRowY)
      minRowY = y_;
    dpRow *tmprow = new dpRow(x_, y_);
    sortedRows.push_back(tmprow);
  }
  sort(sortedRows.begin(), sortedRows.end(), &comparator3);

  auto comparatorLambda2 = [](const CellRPA lhs, const CellRPA rhs) {
    return lhs.lly_ < rhs.lly_;
  };

  dint_ = site_width_ * 3;
  sort(cellrpas_.begin(), cellrpas_.end(), comparatorLambda2);
  updateRow(cellrpas_row_, cellrpas_, sortedRows);
  logger_->report("Started Access point generation");
  GenerateAP(dint_);
  logger_->report("Started RPA computation");
  ComputeRPA(dint_, cellrpas_row_);
  for (int i = 0; i < cells_.size(); i++) {
    id2index[cells_[i].db_inst_->getId()] = i;
  }

  logger_->report("swaprange is {:d} shift range is {:d} and iter is {:d}",
                  swaprange, shiftrange, iter);

  for (int i = 0; i < iter; i++) {
    // logger_->report("Starting Swap and Shift");
    // swap(tmpCells_, sortedRows, id2index);
    SwapAndShift(swaprange, shiftrange, tmpCells_, sortedRows, id2index);
    // logger_->report("Starting only Swap");
  }

  double hpwl_final = hpwl();
  end = std::chrono::system_clock::now();
  std::chrono::duration<double> elapsed_seconds = end - start;

  logger_->report("Elapsed time: {:10.1f} s", elapsed_seconds.count());
  logger_->report("HPWL before shift&swap&flip {:10.1f} u", dbuToMicrons(hpwl_actual));
  // double hpwl_legal = hpwl();
  logger_->report("Final HPWL: {:10.1f} u", dbuToMicrons(hpwl_final));
  double hpwl_delta = (hpwl_actual == 0.0)
      ? 0.0
      : (hpwl_final - hpwl_actual) / hpwl_actual * 100;
  logger_->report("Delta HPWL: {:10.2f} %", hpwl_delta);
}

void
Opendp::swap(vector<Cell> &tmpCells_, vector<dpRow *> &sortedRows,
              map<int, int> &id2index)
{
  vector<vector<Cell *>> all;
  updateRow(all, tmpCells_, sortedRows);
  int i = 0;
  int count = 0;

  for (i = 0; i < all.size(); i++) {
    for (int j = 0; j < all[i].size() - 1; j++) {
      int cellPtX = 0;
      int cellPtY = 0;
      // position for cell 2
      int cellPtXX = 0;
      int cellPtYY = 0;
      all[i][j]->db_inst_->getLocation(cellPtX, cellPtY);
      all[i][j + 1]->db_inst_->getLocation(cellPtXX, cellPtYY);
      vector<Move *> onlyFlip;
      vector<Move *> moves;
      // only flip not swap
      Move *movv1 = new Move(cellPtX, 0, true);
      onlyFlip.push_back(movv1);
      hpwl_increment(all[i][j]->db_inst_, onlyFlip);
      // flip then swap
      Move *movv2 =
        new Move(cellPtXX + all[i][j + 1]->width_ - all[i][j]->width_, 0, true);
      // swap but not flip
      Move *movv3 =
        new Move(cellPtXX + all[i][j + 1]->width_ - all[i][j]->width_, 0, false);

      moves.push_back(movv2);
      moves.push_back(movv3);

      // for the other cell
      vector<dbInst *> other;
      other.push_back(all[i][j + 1]->db_inst_);
      vector<Move *> movess;
      Move *movv4 = new Move(cellPtX, 0, false);
      movess.push_back(movv4);
      hpwl_increment(all[i][j]->db_inst_, moves, other, movess);

      Move *best = movv1;
      for (int k = 0; k < moves.size(); k++) {
        if (best->delta > moves[k]->delta) {
          best = moves[k];
        }
      }
      Cell *temp = all[i][j];
      Cell *tempp = all[i][j + 1];

      if (best->delta < 0) {
        // do the according movement;
        if (best->flip) {
          all[i][j]->orient_ = orientMirrorY(all[i][j]->orient_);
          // printf("flip count is %d\n", count);
        }

        if (best->movement != cellPtX) {
          // printf("predicted is %f\n",(double)best->delta);
          if (swapCellss(all[i][j], all[i][j + 1]) == true) {
            count++;
            // printf("swap count is %d\n", count);
            all[i][j] = all[i][j + 1];
            all[i][j + 1] = temp;
          }
        }

        // update optional info
        int displacement = disp(temp);
        displacement_sum_ += displacement;
        if (displacement > displacement_max_) {
          displacement_max_ = displacement;
        }
        displacement_avg_ = displacement_sum_ / cells_.size();
        if (!isFixed(temp)) {
          dbInst *db_inst_ = temp->db_inst_;
          // Only move the instance if necessary to avoid triggering callbacks.
          if (db_inst_->getOrient() != temp->orient_) {
            db_inst_->setOrient(temp->orient_);
          }
          int x = core_.xMin() + temp->x_;
          int y = core_.yMin() + temp->y_;
          int inst_x, inst_y;
          db_inst_->getLocation(inst_x, inst_y);
          if (x != inst_x || y != inst_y)
            db_inst_->setLocation(x, y);
        }
        if (best->movement != cellPtX) {
          displacement = disp(tempp);
          displacement_sum_ += displacement;
          if (displacement > displacement_max_) {
            displacement_max_ = displacement;
          }
          displacement_avg_ = displacement_sum_ / cells_.size();
          if (!isFixed(tempp)) {
            dbInst *db_inst_ = tempp->db_inst_;
            // Only move the instance if necessary to avoid triggering callbacks.
            if (db_inst_->getOrient() != tempp->orient_)
              db_inst_->setOrient(tempp->orient_);
            int x = core_.xMin() + tempp->x_;
            int y = core_.yMin() + tempp->y_;
            int inst_x, inst_y;
            db_inst_->getLocation(inst_x, inst_y);
            if (x != inst_x || y != inst_y)
              db_inst_->setLocation(x, y);
          }
        }
      }
    }
  }
  for (i = 0; i < 1; i++) {
    for (int j = 0; j < 1; j++) {
      cells_[id2index[all[i][j]->db_inst_->getId()]] = *all[i][j];
    }
  }
}

void
Opendp::SwapAndShift(int MaxForSwap, int MaxForMove, vector<Cell> &tmpCells_,
                      vector<dpRow *> &sortedRows, map<int, int> &id2index)
{
  int alpha = 150;
  vector<vector<Cell *>> all;
  int i = 0;
  updateRow(all, tmpCells_, sortedRows);
  i = 0;

  int count = 0;
  for (i = 0; i < all.size(); i++) {
    // logger_->report("Print all {:d}",all.size());
    for (int j = 0; j < all[i].size(); j++) {
      // logger_->report("Print all_i {:d}",all[i].size());
      // hpwl_before = hpwl();
      vector<int> swaps;
      // get all swappable cells
      for (int x = 0; x < all[i].size(); x++) {
        int distance = MaxForSwap * site_width_;
        // logger_->report("Distance {:d}", distance);
        if ((all[i][x]->x_ >= (all[i][j]->x_ - distance)) &
            ((all[i][x]->x_ + all[i][x]->width_) <=
            (all[i][j]->x_ + all[i][j]->width_ + distance))) {
          // logger_->report("first if passed");
          if (checkSwap(j, x, all[i])) {
            // logger_->report("Check swap succeed");
            swaps.push_back(x);
          } else {
            // logger_->report("Check swap failed");
          }
        } else {
          // logger_->report("first if not passed");
        }
      }
      // update the move vector with all possible movement

      float delta_track = FLT_MAX;
      int cell_track = -1;
      Move *best = new Move();
      vector<Move *> moves;
      vector<dbInst *> other;
      vector<Move *> othermove;
      // logger_->report("Swap size {:d}",swaps.size());
      for (int k = 0; k < swaps.size(); k++) {
        // for the other cell
        if (j != swaps[k]) {
          other.push_back(all[i][swaps[k]]->db_inst_);
          int cellPtX = 0;
          int cellPtY = 0;
          all[i][j]->db_inst_->getLocation(cellPtX, cellPtY);
          Move *movv = new Move(cellPtX, 0, false);
          othermove.push_back(movv);
        }
        // get all movement for the main cell
        for (int n = -MaxForMove; n < MaxForMove + 1; n++) {
          // check if movement after swap is valid
          if (checkValid(j, swaps[k], n, all[i])) {
            int cellPtX = 0;
            int cellPtY = 0;
            all[i][swaps[k]]->db_inst_->getLocation(cellPtX, cellPtY);
            if (((cellPtX + (n * site_width_) - core_.xMin() -
                padLeft(all[i][swaps[k]]) * site_width_) >= 0) &
                (all[i][all[i].size() - 1]->x_ +
                all[i][all[i].size() - 1]->width_ >=
                all[i][swaps[k]]->x_ + (n * site_width_) + all[i][j]->width_)) {
              Move *movv1 = new Move(cellPtX + (n * site_width_), 0, true);
              // not flip
              Move *movv2 = new Move(cellPtX + (n * site_width_), 0, false);
              moves.push_back(movv1);
              moves.push_back(movv2);
            }
          }
        }
        // logger_->report("Outside if");
        if (j != swaps[k]) {
          rpaSwapIncrement(i, j, swaps[k], moves, dint_, 0);
          // rpaSwapIncrement(cellrpas_row_[i], j, swaps[k], moves, dint_);
          for (int m = 0; m < moves.size(); m++) {
            int cellPtX = 0;
            int cellPtY = 0;
            all[i][swaps[k]]->db_inst_->getLocation(cellPtX, cellPtY);
            moves[m]->delta *= alpha;
          }
          hpwl_increment(all[i][j]->db_inst_, moves, other, othermove);
        } else {
          hpwl_increment(all[i][j]->db_inst_, moves);
        }

        for (int m = 0; m < moves.size(); m++) {
          if (delta_track > moves[m]->delta) {
            delta_track = moves[m]->delta;
            cell_track = swaps[k];
            best = moves[m];
          }
        }
        moves.clear();
        other.clear();
        othermove.clear();
      }
      if (delta_track < 0) {
        Cell *temp = all[i][j];

        Cell *tempp = all[i][cell_track];
        dbOrientType orient = all[i][j]->db_inst_->getOrient();
        // do the according movement;

        if (cell_track != j && cell_track != -1) {
          count++;
          int grid_x1 = (best->movement - core_.xMin() -
                        padLeft(tempp) * site_width_)/site_width_;
          int grid_y1 = gridY(tempp);
          int grid_x2 = gridPaddedX(temp);
          int grid_y2 = gridY(temp);

          erasePixel(temp);
          erasePixel(tempp);
          paintPixel(temp, grid_x1, grid_y1);
          paintPixel(tempp, grid_x2, grid_y2);

          all[i][j] = all[i][cell_track];
          all[i][cell_track] = temp;
          CellRPA *swapRPACell = cellrpas_row_[i][j];
          cellrpas_row_[i][j] = cellrpas_row_[i][cell_track];
          cellrpas_row_[i][cell_track] = swapRPACell;
        } else {
          int cellPtXXX = 0;
          int cellPtYYY = 0;
          all[i][j]->db_inst_->getLocation(cellPtXXX, cellPtYYY);
          if ((cell_track != -1) & (best->movement != cellPtXXX)) {
            int grid_x1 = (best->movement - core_.xMin() -
                          padLeft(temp) * site_width_) / site_width_;
            int grid_y1 = gridY(temp);

            erasePixel(temp);
            paintPixel(temp, grid_x1, grid_y1);
          }
        }

        if (best->flip && cell_track != -1) {
          all[i][j]->orient_ = orientMirrorY(orient);
          cellrpas_row_[i][j]->is_flipped_ = !cellrpas_row_[i][j]->is_flipped_;
        }
        // update optional info
        int displacement = disp(temp);
        displacement_sum_ += displacement;
        if (displacement > displacement_max_) {
          displacement_max_ = displacement;
        }
        displacement_avg_ = displacement_sum_ / cells_.size();
        if (!isFixed(temp)) {
          dbInst *db_inst_ = temp->db_inst_;
          // Only move the instance if necessary to avoid triggering callbacks.
          int x = core_.xMin() + temp->x_;
          int y = core_.yMin() + temp->y_;
          int inst_x, inst_y;
          db_inst_->getLocation(inst_x, inst_y);

          if (db_inst_->getOrient() != temp->orient_) {
            db_inst_->setOrient(temp->orient_);
            // printf("yeah!\n");
            if (x == inst_x) {
              rpaIncrementUpdate(j - 1, j + 1, i, dint_);
            }
          }

          if (x != inst_x || y != inst_y) {
            db_inst_->setLocation(x, y);
            cellrpas_row_[i][j]->llx_ = temp->x_;
            rpaIncrementUpdate(j - 1, j + 1, i, dint_);
          }
        }
        if (cell_track != j) {
          displacement = disp(tempp);
          displacement_sum_ += displacement;
          if (displacement > displacement_max_) {
            displacement_max_ = displacement;
          }
          displacement_avg_ = displacement_sum_ / cells_.size();
          if (!isFixed(tempp)) {
            dbInst *db_inst_ = tempp->db_inst_;
            // Only move the instance if necessary to avoid triggering callbacks.
            if (db_inst_->getOrient() != tempp->orient_)
              db_inst_->setOrient(tempp->orient_);
            int x = core_.xMin() + tempp->x_;
            int y = core_.yMin() + tempp->y_;
            int inst_x, inst_y;
            db_inst_->getLocation(inst_x, inst_y);
            if (x != inst_x || y != inst_y) {
              db_inst_->setLocation(x, y);
              cellrpas_row_[i][cell_track]->llx_ = tempp->x_;
              rpaIncrementUpdate(cell_track - 1, cell_track + 1, i, dint_);
            }
          }
          // double hpwl_after = hpwl();
        }
      }
    }
  }
  for (i = 0; i < 1; i++) {
    for (int j = 0; j < 1; j++) {
      cells_[id2index[all[i][j]->db_inst_->getId()]] = *all[i][j];
    }
  }
}

////////////////////////////////////////////////////////////////
void
Opendp::findDisplacementStats()
{
  displacement_avg_ = 0;
  displacement_sum_ = 0;
  displacement_max_ = 0;

  for (const Cell &cell : cells_) {
    int displacement = disp(&cell);
    displacement_sum_ += displacement;
    if (displacement > displacement_max_) {
      displacement_max_ = displacement;
    }
  }
  if (cells_.size())
    displacement_avg_ = displacement_sum_ / cells_.size();
  else
    displacement_avg_ = 0.0;
}

// Note that this does NOT use cell/core coordinates.
int64_t
Opendp::hpwl() const
{
  int64_t hpwl_sum = 0;
  for (dbNet *net : block_->getNets())
    hpwl_sum += hpwl(net);
  return hpwl_sum;
}

int64_t
Opendp::hpwl(dbNet *net) const
{
  if (isSupply(net))
    return 0;
  else {
    Rect bbox = getBox(net);
    return bbox.dx() + bbox.dy();
  }
}

bool
Opendp::isSupply(dbNet *net) const
{
  dbSigType sig_type = net->getSigType();
  return sig_type == dbSigType::POWER || sig_type == dbSigType::GROUND;
}

Rect
Opendp::getBox(dbNet *net) const
{
  Rect net_box;
  net_box.mergeInit();

  for (dbITerm *iterm : net->getITerms()) {
    int x, y;
    if (iterm->getAvgXY(&x, &y)) {
      Rect iterm_rect(x, y, x, y);
      net_box.merge(iterm_rect);
    } else {
      // This clause is sort of worthless because getAvgXY prints
      // a warning when it fails.
      dbInst *inst = iterm->getInst();
      dbBox *inst_box = inst->getBBox();
      int center_x = (inst_box->xMin() + inst_box->xMax()) / 2;
      int center_y = (inst_box->yMin() + inst_box->yMax()) / 2;
      Rect inst_center(center_x, center_y, center_x, center_y);
      net_box.merge(inst_center);
    }
  }

  for (dbBTerm *bterm : net->getBTerms()) {
    for (dbBPin *bpin : bterm->getBPins()) {
      dbPlacementStatus status = bpin->getPlacementStatus();
      if (status.isPlaced()) {
        Rect pin_bbox = bpin->getBBox();
        int center_x = (pin_bbox.xMin() + pin_bbox.xMax()) / 2;
        int center_y = (pin_bbox.yMin() + pin_bbox.yMax()) / 2;
        Rect pin_center(center_x, center_y, center_x, center_y);
        net_box.merge(pin_center);
      }
    }
  }
  return net_box;
}

////////////////////////////////////////////////////////////////

Power
Opendp::rowTopPower(int row) const
{
  return ((row0_top_power_is_vdd_ ? row : row + 1) % 2 == 0) ? VDD : VSS;
}

dbOrientType
Opendp::rowOrient(int row) const
{
  // Row orient flips R0 -> MX -> R0 -> MX ...
  return ((row0_orient_is_r0_ ? row : row + 1) % 2 == 0) ? dbOrientType::R0
                                                         : dbOrientType::MX;
}

////////////////////////////////////////////////////////////////

Point
Opendp::initialLocation(const Cell *cell,
                        bool padded) const
{
  int loc_x, loc_y;
  cell->db_inst_->getLocation(loc_x, loc_y);
  loc_x -= core_.xMin();
  if (padded)
    loc_x -= padLeft(cell) * site_width_;
  loc_y -= core_.yMin();
  return Point(loc_x, loc_y);
}

int
Opendp::disp(const Cell *cell) const
{
  Point init = initialLocation(cell, false);
  return abs(init.getX() - cell->x_) + abs(init.getY() - cell->y_);
}

bool
Opendp::isPaddedType(dbInst *inst) const
{
  dbMasterType type = inst->getMaster()->getType();
  // Use switch so if new types are added we get a compiler warning.
  switch (type) {
    case dbMasterType::CORE:
    case dbMasterType::CORE_ANTENNACELL:
    case dbMasterType::CORE_FEEDTHRU:
    case dbMasterType::CORE_TIEHIGH:
    case dbMasterType::CORE_TIELOW:
    case dbMasterType::CORE_WELLTAP:
    case dbMasterType::ENDCAP:
    case dbMasterType::ENDCAP_PRE:
    case dbMasterType::ENDCAP_POST:
      return true;
    case dbMasterType::CORE_SPACER:
    case dbMasterType::BLOCK:
    case dbMasterType::BLOCK_BLACKBOX:
    case dbMasterType::BLOCK_SOFT:
    case dbMasterType::ENDCAP_TOPLEFT:
    case dbMasterType::ENDCAP_TOPRIGHT:
    case dbMasterType::ENDCAP_BOTTOMLEFT:
    case dbMasterType::ENDCAP_BOTTOMRIGHT:
      // These classes are completely ignored by the placer.
    case dbMasterType::COVER:
    case dbMasterType::COVER_BUMP:
    case dbMasterType::RING:
    case dbMasterType::PAD:
    case dbMasterType::PAD_AREAIO:
    case dbMasterType::PAD_INPUT:
    case dbMasterType::PAD_OUTPUT:
    case dbMasterType::PAD_INOUT:
    case dbMasterType::PAD_POWER:
    case dbMasterType::PAD_SPACER:
    case dbMasterType::NONE:
      return false;
  }
  // gcc warniing
  return false;
}

bool
Opendp::isStdCell(const Cell *cell) const
{
  dbMasterType type = cell->db_inst_->getMaster()->getType();
  // Use switch so if new types are added we get a compiler warning.
  switch (type) {
    case dbMasterType::CORE:
    case dbMasterType::CORE_ANTENNACELL:
    case dbMasterType::CORE_FEEDTHRU:
    case dbMasterType::CORE_TIEHIGH:
    case dbMasterType::CORE_TIELOW:
    case dbMasterType::CORE_SPACER:
    case dbMasterType::CORE_WELLTAP:
      return true;
    case dbMasterType::BLOCK:
    case dbMasterType::BLOCK_BLACKBOX:
    case dbMasterType::BLOCK_SOFT:
    case dbMasterType::ENDCAP:
    case dbMasterType::ENDCAP_PRE:
    case dbMasterType::ENDCAP_POST:
    case dbMasterType::ENDCAP_TOPLEFT:
    case dbMasterType::ENDCAP_TOPRIGHT:
    case dbMasterType::ENDCAP_BOTTOMLEFT:
    case dbMasterType::ENDCAP_BOTTOMRIGHT:
      // These classes are completely ignored by the placer.
    case dbMasterType::COVER:
    case dbMasterType::COVER_BUMP:
    case dbMasterType::RING:
    case dbMasterType::PAD:
    case dbMasterType::PAD_AREAIO:
    case dbMasterType::PAD_INPUT:
    case dbMasterType::PAD_OUTPUT:
    case dbMasterType::PAD_INOUT:
    case dbMasterType::PAD_POWER:
    case dbMasterType::PAD_SPACER:
    case dbMasterType::NONE:
      return false;
  }
  // gcc warniing
  return false;
}

/* static */
bool
Opendp::isBlock(const Cell *cell)
{
  dbMasterType type = cell->db_inst_->getMaster()->getType();
  return type == dbMasterType::BLOCK;
}

int
Opendp::gridEndX() const
{
  return gridEndX(core_.dx());
}

int
Opendp::gridEndY() const
{
  return gridEndY(core_.dy());
}

int
Opendp::padLeft(const Cell *cell) const
{
  return padLeft(cell->db_inst_);
}

int
Opendp::padLeft(dbInst *inst) const
{
  if (isPaddedType(inst)) {
    auto itr1 = inst_padding_map_.find(inst);
    if (itr1 != inst_padding_map_.end())
      return itr1->second.first;
    auto itr2 = master_padding_map_.find(inst->getMaster());
    if (itr2 != master_padding_map_.end())
      return itr2->second.first;
    else
      return pad_left_;
  }
  else
    return 0;
}

int
Opendp::padRight(const Cell *cell) const
{
  return padRight(cell->db_inst_);
}

int
Opendp::padRight(dbInst *inst) const
{
  if (isPaddedType(inst)) {
    auto itr1 = inst_padding_map_.find(inst);
    if (itr1 != inst_padding_map_.end())
      return itr1->second.second;
    auto itr2 = master_padding_map_.find(inst->getMaster());
    if (itr2 != master_padding_map_.end())
      return itr2->second.second;
    else
      return pad_right_;
  }
  else
    return 0;
}

int
Opendp::paddedWidth(const Cell *cell) const
{
  return cell->width_ + (padLeft(cell) + padRight(cell)) * site_width_;
}

int
Opendp::gridPaddedWidth(const Cell *cell) const
{
  return divCeil(paddedWidth(cell), site_width_);
}

int
Opendp::gridHeight(const Cell *cell) const
{
  return divCeil(cell->height_, row_height_);
}

int64_t
Opendp::paddedArea(const Cell *cell) const
{
  return paddedWidth(cell) * cell->height_;
}

// Callers should probably be using gridPaddedWidth.
int
Opendp::gridNearestWidth(const Cell *cell) const
{
  return divRound(paddedWidth(cell), site_width_);
}

// Callers should probably be using gridHeight.
int
Opendp::gridNearestHeight(const Cell *cell) const
{
  return divRound(cell->height_, row_height_);
}

int
Opendp::gridX(int x) const
{
  return x / site_width_;
}

int
Opendp::gridEndX(int x) const
{
  return divCeil(x, site_width_);
}

int
Opendp::gridY(int y) const
{
  return y / row_height_;
}

int
Opendp::gridEndY(int y) const
{
  return divCeil(y, row_height_);
}

int
Opendp::gridX(const Cell *cell) const
{
  return gridX(cell->x_);
}

int
Opendp::gridPaddedX(const Cell *cell) const
{
  return gridX(cell->x_ - padLeft(cell) * site_width_);
}

int
Opendp::gridY(const Cell *cell) const
{
  return gridY(cell->y_);
}

void
Opendp::setGridPaddedLoc(Cell *cell, int x, int y) const
{
  cell->x_ = (x + padLeft(cell)) * site_width_;
  cell->y_ = y * row_height_;
}

int
Opendp::gridPaddedEndX(const Cell *cell) const
{
  return divCeil(cell->x_ + cell->width_ + padRight(cell) * site_width_,
                 site_width_);
}

int
Opendp::gridEndX(const Cell *cell) const
{
  return divCeil(cell->x_ + cell->width_, site_width_);
}

int
Opendp::gridEndY(const Cell *cell) const
{
  return divCeil(cell->y_ + cell->height_, row_height_);
}

double
Opendp::dbuToMicrons(int64_t dbu) const
{
  double dbu_micron = db_->getTech()->getDbUnitsPerMicron();
  return dbu / dbu_micron;
}

double
Opendp::dbuAreaToMicrons(int64_t dbu_area) const
{
  double dbu_micron = db_->getTech()->getDbUnitsPerMicron();
  return dbu_area / (dbu_micron * dbu_micron);
}

int
divRound(int dividend, int divisor)
{
  return round(static_cast<double>(dividend) / divisor);
}

int
divCeil(int dividend, int divisor)
{
  return ceil(static_cast<double>(dividend) / divisor);
}

int
divFloor(int dividend, int divisor)
{
  return dividend / divisor;
}

}  // namespace dpl
