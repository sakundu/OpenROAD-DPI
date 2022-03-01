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
#include "utl/Logger.h"
#include "ord/OpenRoad.hh"  // closestPtInRect

namespace dpl {

using std::round;
using std::string;
using std::vector;

using utl::DPL;

using odb::Point;
using odb::dbBox;
using odb::dbBPin;
using odb::dbBTerm;
using odb::dbITerm;
using odb::dbMasterType;
using odb::dbMPin;
using odb::dbMTerm;
using odb::dbNet;
using odb::dbPlacementStatus;
using odb::Rect;
using odb::dbSigType;
using odb::dbTransform;
using odb::dbOrientType;

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

Move::Move(int64_t Movementt, int64_t deltaa, bool flipp) :
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

////////////////////////////////////////////////////////////////

static bool comparator6(const Pin_RPA lhs, const Pin_RPA rhs) {
   return lhs.x_min < rhs.x_min;
}

static bool comparator4(const AccessPoint lhs, const AccessPoint rhs) {
   return lhs.x < rhs.x;
}

static bool comparator5(const AccessPoint lhs, const AccessPoint rhs) {
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
  return pad_left_ > 0 || pad_right_ > 0
    || !master_padding_map_.empty()
    || !inst_padding_map_.empty();
}

void
Opendp::setDebug(bool displacement,
                 float min_displacement,
                 const dbInst* debug_instance)
{
  if (Graphics::guiActive()) {
    graphics_ = std::make_unique<Graphics>(this,
                                           min_displacement,
                                           debug_instance);
  }
}

void
Opendp::updateRow(vector<vector<Cell_RPA *>> &all, vector<Cell_RPA> &tmpCells_, vector<dpRow *> &sortedRows)
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
      if(db_row_miny == temp->y_ && i == cellCount)
      {
        row.push_back(temp);
      }
      else if(db_row_miny != temp->y_ && i == cellCount)
      {
        row.clear();
        row.push_back(temp);
        all.push_back(row);
        break;
      }
      
      auto compareLambda1 = [](const Cell_RPA *lhs, const Cell_RPA *rhs)
      {
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
        }
        else {
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
          dbMaster* tmpMaster = temp->db_inst_->getMaster();
          logger_->report("Row Y and Cell Y not Matching: Cell Master Name:{:s}",tmpMaster->getName());
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
                    tmpMaster->getName(), temp->x_, temp->y_);
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
Opendp::GenerateAP()
{
  for(Cell_RPA &cell: cell_rpas_)
  {
    int px;
    int py;
    cell.db_inst_->getOrigin(px, py);
    dbOrientType orient = cell.db_inst_->getOrient();
    Point origin = Point(px, py);
    dbTransform inst_xfm(orient, origin);

    odb::dbMaster *master = cell.db_inst_->getMaster();
    for ( dbMTerm *mterm: master->getMTerms()) {
      // No need to find access point for power pins
      if ( mterm->getSigType().isSupply())
        continue;  
      
      for ( dbMPin *mpin: mterm->getMPins()) {
        odb::dbSet<odb::dbBox> pinshapes = mpin->getGeometry();
        odb::Rect pinbox = mpin->getBBox();
        inst_xfm.apply(pinbox);
        Pin_RPA newPin;
        newPin.mpin = mpin;
        newPin.x_min = pinbox.xMin();

        for ( odb::dbBox *pinshape: pinshapes) {
          Rect shapeBox;
          pinshape->getBox(shapeBox);
          inst_xfm.apply(shapeBox);
          odb::dbTechLayer* pinLayer = pinshape->getTechLayer();
          odb::dbTechLayerType lType = pinLayer->getType();

          if ( lType == odb::dbTechLayerType::Value::ROUTING) {
            // Find the upper pin layer
            odb::dbTechLayer *upperPinLayer = pinLayer->getUpperLayer();
            while ( upperPinLayer->getType() != odb::dbTechLayerType::Value::ROUTING) {
              upperPinLayer = upperPinLayer->getUpperLayer();
            }

            odb::dbTrackGrid *tmpGrid = block_->findTrackGrid(upperPinLayer);
            vector<int> xgrid, ygrid;
            
            //vector<pair<int,int>> APs;
            
            tmpGrid->getGridX(xgrid);
            tmpGrid->getGridY(ygrid);

            //check if the shape is vertical or horizontal
            if((shapeBox.xMax() - shapeBox.xMin()) <= (shapeBox.yMax() - shapeBox.yMin()))
            {
              // For Vertical Pin Shapes
              int top = shapeBox.yMax();
              int bot = shapeBox.yMin();
              int ygap = ygrid[1]-ygrid[0];
              int x = (shapeBox.xMax() + shapeBox.xMin())/2;
            
              int count = (top-ygrid[0])/ygap;
              int actualTop = (count * ygap) + ygrid[0];

              for(int i = actualTop; i >= bot; i -= ygap)
              {
                AccessPoint ap;
                ap.x = x;
                ap.y = i;
                ap.layer = pinLayer;
                // We do not store vertical AP in xAPs.
                newPin.xAPs.push_back(ap);
                newPin.yAPs.push_back(ap);
              }
            }
            else
            {
            }
          }
        }

        //After adding all the APS from each shape, sort them
        sort(newPin.xAPs.begin(), newPin.xAPs.end(), &comparator4);
        sort(newPin.yAPs.begin(), newPin.yAPs.end(), &comparator5);
        
        cell.pins.push_back(newPin);
      }
    }

    //after adding all the pins
    sort(cell.pins.begin(), cell.pins.end(), &comparator6);
  }
}

//default dint is 2000
void
Opendp::RPAGenerate(int dint)
{
  //cell_rpas_;
  vector<vector<Cell_RPA*>> cell_rpas;

  auto comparatorLambda2 = [] (const Cell_RPA lhs, const Cell_RPA rhs)
  {
    return lhs.y_ < rhs.y_;
  };

  sort(cell_rpas_.begin(), cell_rpas_.end(), comparatorLambda2);
  
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
  updateRow(cell_rpas,cell_rpas_, sortedRows);

  // RPA Computation starts
  for (int i = 0; i < cell_rpas.size(); i++) {
    for (int j = 0; j < cell_rpas[i].size(); j++) {
      for(int k = 0; k < cell_rpas[i][j]->pins.size(); k++)
      {
        double xPinRPA = cell_rpas[i][j]->pins[k].xAPs.size();
        double yPinRPA = cell_rpas[i][j]->pins[k].yAPs.size();
        if((xPinRPA == 0) & (yPinRPA == 0))
        {
          cell_rpas[i][j]->rpa = std::min(cell_rpas[i][j]->rpa, -2.0);
        }
        string pinName = cell_rpas[i][j]->pins[k].mpin->getMTerm()->getName();
        string cellName = cell_rpas[i][j]->db_inst_->getName();
        logger_->report("Cell:{:s} Pin:{:s}",cellName, pinName);
        for(AccessPoint APmain : cell_rpas[i][j]->pins[k].xAPs)
        {
          for(int l = 1; l < 4; l++)
          {
            //check left neighbors
            if((k-l) < 0)
            {
              if((j-1) >= 0)
              {
                int size = cell_rpas[i][j-1]->pins.size();
                double rpaTrack = 0;
                if((size+(k-l)) >= 0)
                {
                  for(AccessPoint APneib : cell_rpas[i][j-1]->pins[size+(k-l)].xAPs)
                  {
                    if((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer))
                    {
                      rpaTrack += 1;
                    }
                  }
                  if(cell_rpas[i][j-1]->pins[size+(k-l)].xAPs.size() != 0)
                  {
                    double upa = rpaTrack/cell_rpas[i][j-1]->pins[size+(k-l)].xAPs.size();
                    xPinRPA = xPinRPA - upa;
                    logger_->report("UAP: {:f}", upa);
                  }
                }
              }
            }
            //neighbor is inside main cell
            else
            {
              double rpaTrack = 0;
              for(AccessPoint APneib : cell_rpas[i][j]->pins[k-l].xAPs)
              {
                if((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer))
                {
                  rpaTrack += 1;
                }
              }
              if(cell_rpas[i][j]->pins[k-l].xAPs.size() != 0)
              {
                double upa = rpaTrack/cell_rpas[i][j]->pins[k-l].xAPs.size();
                xPinRPA = xPinRPA - upa;
                logger_->report("UAP: {:f}", upa);
              }
            }
            //check right nerghbors
            //right neighbor is not in main cell
            if((k+l) >= cell_rpas[i][j]->pins.size())
            {
              if((j+1) < cell_rpas[i].size())
              {
                //int size = cell_rpas[i][j+1]->pins.size();
                double rpaTrack = 0;
                int index = k+l-cell_rpas[i][j]->pins.size();
                if(index < cell_rpas[i][j+1]->pins.size())
                {
                  for(AccessPoint APneib : cell_rpas[i][j+1]->pins[index].xAPs)
                  {
                    if((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer))
                    {
                      rpaTrack += 1;
                    }
                  }
                  if(cell_rpas[i][j+1]->pins[index].xAPs.size() != 0)
                  {
                    double upa = rpaTrack/cell_rpas[i][j+1]->pins[index].xAPs.size();
                    xPinRPA = xPinRPA - upa;
                    logger_->report("UAP: {:f}", upa);
                  }
                }
              }
            }
            //neighbor is inside main cell
            else
            {
              double rpaTrack = 0;
              for(AccessPoint APneib : cell_rpas[i][j]->pins[k+l].xAPs)
              {
                if((std::abs(APmain.x - APneib.x) <= dint) & (APmain.y == APneib.y) & (APmain.layer == APneib.layer))
                {
                  rpaTrack += 1;
                }
              }
              if(cell_rpas[i][j]->pins[k+l].xAPs.size() != 0)
              {
                double upa = rpaTrack/cell_rpas[i][j]->pins[k+l].xAPs.size();
                xPinRPA = xPinRPA - upa;
                logger_->report("UAP: {:f}", upa);
              }
            }
          }
        }
        xPinRPA -= 1;
        yPinRPA -= 1;
        
        logger_->report("Cell:{:s} Pin:{:s} RPA:{:f}",cellName, pinName, xPinRPA);
        //double minPinRPA = xPinRPA < yPinRPA?xPinRPA:yPinRPA;
        cell_rpas[i][j]->rpa += xPinRPA < 0 ? xPinRPA : 0;
        //cell_rpas[i][j]->rpa = cell_rpas[i][j]->rpa < minPinRPA?cell_rpas[i][j]->rpa:minPinRPA ;
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
  }
  else {
    max_displacement_x_ = max_displacement_x;
    max_displacement_y_ = max_displacement_y;
  }

  reportImportWarnings();
  hpwl_before_ = hpwl();
  detailedPlacement();
  // Save displacement stats before updating instance DB locations.
  findDisplacementStats();
  updateDbInstLocations();
  logger_->report("Starting Access Point Generator.");
  GenerateAP();
  logger_->report("Starting RPA Generator.");
  RPAGenerate(500);
  
  char s1 = '{', s2 = '}';
  
  for(Cell_RPA cell: cell_rpas_)
  {
    //if(cell.db_inst_->getName() == "_33512_")
    //{
      logger_->report("Cell name : {:s}, pin count : {:d}, rpa value: {:f}", cell.db_inst_->getName(), cell.pins.size(), cell.rpa);
      for(Pin_RPA pin: cell.pins)
      {
        logger_->report("Pin name : {:s}, PA count : {:d}", pin.mpin->getMTerm()->getName(), pin.xAPs.size());
        for(AccessPoint ap: pin.xAPs)
        {
          float x = ap.x/dbUnit;
          float y = ap.y/dbUnit;
          //logger_->report("Access point x : {:d}, y : {:d}", ap.x, ap.y);
          logger_->report("createMarker -bbox {:c}{:f} {:f} {:f} {:f}{:c}",s1,x,y,x,y,s2);
        }
      }
  }

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
comparator2(const Cell *lhs, const Cell *rhs)
{
  return lhs->x_ < rhs->x_;
}

bool
Opendp::checkSwap(int i, int j, vector<Cell *> row)
{
  if (row[i]->hold_ || row[j]->hold_ || isFixed(row[i]) || isFixed(row[j]) || !row[i]->is_placed_ || !row[j]->is_placed_) {
    return false;
  }
  int check1 = 10;
  int check2 = 10;
  if (i + 1 < row.size()) {
    check1 = (row[i + 1]->x_ - padLeft(row[i]) * site_width_ * 2 - (row[i]->x_ + row[j]->width_)) / site_width_;
  }
  if (j + 1 < row.size()) {
    check2 = (row[j + 1]->x_ - padLeft(row[j]) * site_width_ * 2 - (row[j]->x_ + row[i]->width_)) / site_width_;
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
Opendp::hpwl_increment(dbInst *inst, vector<dbITerm *> iterms, dbNet *net, int pt_x, bool mirror) const
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
    }
    else {
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
      }
      else {
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
      }
      else {
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
    }
    else {
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
    check1 = (row[swapcell + 1]->x_ - (row[swapcell]->x_ + row[origincell]->width_) - padLeft(row[swapcell]) * site_width_ * 2 - shift * site_width_) / site_width_;
  }
  else {
    if ((row[swapcell]->x_ + row[origincell]->width_ + shift * site_width_) > (row[swapcell]->x_ + row[swapcell]->width_)) {
      return false;
    }
  }
  if ((swapcell - 1) != origincell) {
    if (swapcell - 1 >= 0) {
      check2 = (row[swapcell]->x_ - (row[swapcell - 1]->x_ + row[swapcell - 1]->width_) - padLeft(row[swapcell]) * site_width_ * 2 + shift * site_width_) / site_width_;
    }
  }
  else {
    check2 = (row[swapcell]->x_ - (row[swapcell - 1]->x_ + row[swapcell]->width_) - padLeft(row[swapcell]) * site_width_ * 2 + shift * site_width_) / site_width_;
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
Opendp::hpwl_increment(dbInst *inst, vector<dbITerm *> iterms, dbNet *net, vector<Move *> moves)
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
    }
    else {
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
        }
        else {
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
Opendp::hpwl_increment( dbInst *inst, vector<Move *> moves, 
                        vector<dbInst *> others, vector<Move *> movess)
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
    }
    else {
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
      }
      else {
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
Opendp::hpwl_increment( dbInst *inst, vector<dbITerm *> iterms, dbNet *net, vector<Move *> moves, 
                        vector<vector<vector<dbITerm *>>> itermss, vector<dbInst *> others, 
                        vector<Move *> movess, int netCount )
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
    }
    else {
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
    }
    else {
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
      }
      else {
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
          i = std::find(itermss[j][netCount].begin(), itermss[j][netCount].end(), iterm_) - itermss[j][netCount].begin();
          if (i < itermss[j][netCount].size()) {
            check = true;
            break;
          }
        }
      }
      else {
        check = true;
      }
      if (!check) {
        int x, y;
        if (iterm_->getAvgXY(&x, &y)) {
          Rect iterm_rect_(x, y, x, y);
          new_net_box.merge(iterm_rect_);
        }
        else {
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
  if (cell1 != cell2 && !cell1->hold_ && !cell2->hold_ && !isFixed(cell1) && !isFixed(cell2))
  {
    if (cell2->x_ > cell1->x_) 
    {
      int temp = cell2->x_ + cell2->width_ - cell1->width_ - padLeft(cell1) * site_width_;
      int grid_x1 = temp/site_width_;
      int grid_y1 = gridY(cell2);
      int grid_x2 = gridPaddedX(cell1);
      int grid_y2 = gridY(cell1);
      erasePixel(cell1);
      erasePixel(cell2);
      paintPixel(cell2, grid_x2, grid_y2);
      paintPixel(cell1, grid_x1, grid_y1);
    }
    else 
    {
      int temp = cell1->x_ + cell1->width_ - cell2->width_ - padLeft(cell1) * site_width_;
      int grid_x2 = (temp)/site_width_;
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
Opendp::updateRow(vector<vector<Cell *>> &all, vector<Cell> &tmpCells_, vector<dpRow *> &sortedRows)
{
  //sort(tmpCells_.begin(), tmpCells_.end(), &comparator1);
  int cellCount = (int)tmpCells_.size();
  
  int i = 0;

  int rowSize = sortedRows.size();
  //logger_->report("Probelm is in the sort funciton");
  //sort(sortedRows.begin(), sortedRows.end(), &comparator3);
  //logger_->report("Probelm is not in the sort funciton");
  
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
    // logger_->report("ROW:{:d} Cell:{:d} ROW Y:{:d} Cell Y:{:d}", j, i, db_row_miny, temp->y_);
    if (db_row_miny != temp->y_ || i == cellCount) {
      if(db_row_miny == temp->y_ && i == cellCount)
      {
        row.push_back(temp);
      }
      else if(db_row_miny != temp->y_ && i == cellCount)
      {
        row.clear();
        row.push_back(temp);
        all.push_back(row);
        break;
      }
      sort(row.begin(), row.end(), &comparator2);
      vector<Cell *> tmprow;
      int rowLength = row.size();
      int k = 0;
      //Cell *cell = row[k];
      // logger_->report("\nRow Cell Count:{:d} Row:{:d}/{:d} Cell:{:d}/{:d}", rowLength,j,rowSize,i,cellCount);
      while (k <= rowLength) {
        if (k < rowLength && row[k]->x_ < db_row_maxx) {
          // logger_->report("Row:[{:d},{:d}] Y:{:d} X:{:d}, Cell Y:{:d} X:{:d}", j, k, db_row_miny, db_row_maxx, row[k]->y_, row[k]->x_);
          tmprow.push_back(row[k]);
          k++;
        }
        else {
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
          dbMaster* tmpMaster = temp->db_inst_->getMaster();
          logger_->report("Row Y and Cell Y not Matching: Cell Master Name:{:s}",tmpMaster->getName());
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
    //dbMaster *tmpMaster = temp->db_inst_->getMaster();
    //logger_->report("Row:{:d}/{:d} Cell:{:d}/{:d} Current Row Y:{:d} Cell Y:{:d} Master:{:s} MinRowY:{:d} MaxRowY:{:d} CoreY:{:d}", j,rowSize,i,cellCount,db_row_miny,temp->y_,tmpMaster->getName(),minRowY,maxRowY,core_.yMin());
  }
  while (j == rowSize && i < cellCount) {
    temp = &tmpCells_[i];
    dbMaster *tmpMaster = temp->db_inst_->getMaster();
    logger_->report("Cells not able to find any valid row Cell:{:s} X:{:d} Y:{:d}", 
                    tmpMaster->getName(), temp->x_, temp->y_);
    i++;
  }
  // logger_->report("Update Row is Finished");
}

void
Opendp::RPATest()
{
  // Initialize opendp
  importDb();
  initGrid();

  // Paint fixed cells.
  setFixedGridCells();

  //Get def detials
  float dbUnit = 1.0*(block_->getDefUnits());
  
  // Set to store unique pin layers
  set<odb::dbTechLayer*> pinLayers;
  char s1 = '{', s2 = '}';
  // Below code is used to check if dbTransformation is 
  // working properly or not for extracted cell pin shapes
  // Below code is to find the cell pin layers in the block
  vector<dbMaster*> masterList;
  block_->getMasters(masterList);
  for ( dbMaster* master: masterList) {
    for ( dbMTerm* mterm: master->getMTerms()) {
      if ( mterm->getSigType().isSupply())
        continue;
      for ( dbMPin* mpin: mterm->getMPins()) {
        odb::dbSet<odb::dbBox> pinShapes = mpin->getGeometry();
        for (odb::dbBox *pinShape: pinShapes) {
          odb::dbTechLayer *pinLayer = pinShape->getTechLayer();
          odb::dbTechLayerType pinLayerType = pinLayer->getType();
          if ( pinLayerType != odb::dbTechLayerType::Value::ROUTING)
            continue;
          pinLayers.insert(pinLayer);
        }
      }
    }
  }

  // Get details of the pin layers
  for (odb::dbTechLayer *pinLayer: pinLayers) {
    odb::dbTrackGrid *tmpGrid = block_->findTrackGrid(pinLayer);
    vector<int> xgrid, ygrid;

    if ( tmpGrid != nullptr) {
      tmpGrid->getGridX(xgrid);
      tmpGrid->getGridY(ygrid);
    }

    int xOffset = xgrid[0], yOffset = ygrid[0], xPitch = xgrid[1] - xgrid[0], 
      yPitch = ygrid[1] - ygrid[0];
    string pinLayerName = pinLayer->getName();
    odb::dbTechLayerDir pinLayerDirection = pinLayer->getDirection();
    
    const char *layerDirectoin = pinLayerDirection.getString();

    logger_->report("Pin Layer:{:s} X Offset:{:d} Pitch:{:d}\tY Offset:{:d} Pitch:{:d} Directoin:{:s}",
    pinLayerName, xOffset, xPitch, yOffset, yPitch, layerDirectoin);

    // Get upper and lower layer details
    odb::dbTechLayer *upperPinLayer = pinLayer->getUpperLayer();
    while ( upperPinLayer->getType() != odb::dbTechLayerType::Value::ROUTING) {
      upperPinLayer = upperPinLayer->getUpperLayer();
    }

    string upperLayerName = upperPinLayer->getName();
    logger_->report("Pin Layer:{:s} Upper Layer:{:s}", pinLayerName, upperLayerName);
  }

  // Here we test GenerateAP
  
  GenerateAP();
  RPAGenerate(340);
  for (Cell_RPA tmpCell: cell_rpas_) {
    for ( Pin_RPA tmpPin: tmpCell.pins) {
      for (AccessPoint tmpAP: tmpPin.xAPs) {
        float x = tmpAP.x/dbUnit;
        float y = tmpAP.y/dbUnit;
         logger_->report("createMarker -bbox {:c}{:f} {:f} {:f} {:f}{:c} -type AP",s1,x,y,x,y,s2);
      }
    }
  }
  logger_->report("RPA Testing is done");
  
  for ( Cell_RPA tmpCell: cell_rpas_) {
    string cellName = tmpCell.db_inst_->getName();
    dbMaster *master = tmpCell.db_inst_->getMaster();
    string cellMasterName = master->getName();
    logger_->report("Cell Name:{:s} Master Name:{:s} RPA Value:{:f}", cellName, cellMasterName, tmpCell.rpa);
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
  
  map<int,int> id2index;

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

  // for (auto tmpCell: tmpCells_) {
  // logger_->report("Cell ID: {:d} Name: {:s}", tmpCell.db_inst_->getId(), tmpCell.db_inst_->getName());
  // }
  for (int i = 0; i < cells_.size(); i++) {
    id2index[cells_[i].db_inst_->getId()] = i;
  }

  logger_->report("swaprange is {:d} shift range is {:d} and iter is {:d}", swaprange, shiftrange, iter);
  for (int i = 0; i < iter; i++) {
    //logger_->report("Starting Swap and Shift");
    swap(tmpCells_, sortedRows, id2index);
    SwapAndShift(swaprange, shiftrange, tmpCells_, sortedRows, id2index);
    //logger_->report("Starting only Swap");
  }
  double hpwl_final = hpwl();
  end = std::chrono::system_clock::now();
  std::chrono::duration<double> elapsed_seconds = end - start;

  logger_->report("Elapsed time: {:10.1f} s", elapsed_seconds.count());
  logger_->report("HPWL before shift&swap&flip {:10.1f} u", dbuToMicrons(hpwl_actual));
  //double hpwl_legal = hpwl();
  logger_->report("Final HPWL: {:10.1f} u", dbuToMicrons(hpwl_final));
  double hpwl_delta = (hpwl_actual == 0.0)
      ? 0.0
      : (hpwl_final - hpwl_actual) / hpwl_actual * 100;
  logger_->report("Delta HPWL: {:10.2f} %", hpwl_delta);
}

void
Opendp::swap(vector<Cell> &tmpCells_, vector<dpRow *> &sortedRows, map<int,int> &id2index)
{
  vector<vector<Cell *>> all;
  updateRow(all,tmpCells_, sortedRows);
  int i = 0;
  int count = 0;

  for (i = 0; i < all.size(); i++) {
    for (int j = 0; j < all[i].size()-1; j++) {
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
      Move *movv2 = new Move(cellPtXX + all[i][j + 1]->width_ - all[i][j]->width_, 0, true);
      // swap but not flip
      Move *movv3 = new Move(cellPtXX + all[i][j + 1]->width_ - all[i][j]->width_, 0, false);

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
  for(i = 0; i < 1; i ++)
  {
    for(int j = 0; j < 1; j++)
    {
      cells_[id2index[all[i][j]->db_inst_->getId()]] = *all[i][j];
    }
  }
}

void
Opendp::SwapAndShift( int MaxForSwap, int MaxForMove, vector<Cell> &tmpCells_, 
                      vector<dpRow *>& sortedRows, map<int,int> &id2index)
{
  vector<vector<Cell *>> all;
  int i = 0;
  updateRow(all,tmpCells_, sortedRows);
  i = 0;
  
  int count = 0;
  for (i = 0; i < all.size(); i++) {
    for (int j = 0; j < all[i].size(); j++) {
      // hpwl_before = hpwl();
      vector<int> swaps;
      // get all swappable cells
      for (int x = 0; x < all[i].size(); x++) {
        int distance = MaxForSwap * site_width_;
        if ((all[i][x]->x_ >= (all[i][j]->x_ - distance)) & ((all[i][x]->x_ + all[i][x]->width_) <= (all[i][j]->x_ + all[i][j]->width_ + distance))) {
          if (checkSwap(j, x, all[i])) {
            swaps.push_back(x);
          }
        }
      }
      // update the move vector with all possible movement

      int delta_track = INT32_MAX;
      int cell_track = -1;
      Move *best = new Move();
      vector<Move *> moves;
      vector<dbInst *> other;
      vector<Move *> othermove;
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
            if (((cellPtX + (n * site_width_) - core_.xMin() - padLeft(all[i][swaps[k]]) * site_width_) >= 0) & (all[i][all[i].size() - 1]->x_ + all[i][all[i].size() - 1]->width_ >= all[i][swaps[k]]->x_ + (n * site_width_) + all[i][j]->width_)) {
              Move *movv1 = new Move(cellPtX + (n * site_width_), 0, true);
              // not flip
              Move *movv2 = new Move(cellPtX + (n * site_width_), 0, false);
              moves.push_back(movv1);
              moves.push_back(movv2);
            }
          }
        }

        if (j != swaps[k]) {
          hpwl_increment(all[i][j]->db_inst_, moves, other, othermove);
        }
        else {
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
          int grid_x1 = (best->movement - core_.xMin() - padLeft(tempp) * site_width_) / site_width_;
          int grid_y1 = gridY(tempp);
          int grid_x2 = gridPaddedX(temp);
          int grid_y2 = gridY(temp);

          erasePixel(temp);
          erasePixel(tempp);
          paintPixel(temp, grid_x1, grid_y1);
          paintPixel(tempp, grid_x2, grid_y2);

          all[i][j] = all[i][cell_track];
          all[i][cell_track] = temp;
        }
        else 
        {
          int cellPtXXX = 0;
          int cellPtYYY = 0;
          all[i][j]->db_inst_->getLocation(cellPtXXX, cellPtYYY);
          if ((cell_track != -1) & (best->movement != cellPtXXX)) {
            int grid_x1 = (best->movement - core_.xMin() - padLeft(temp) * site_width_) / site_width_;
            int grid_y1 = gridY(temp);

            erasePixel(temp);
            paintPixel(temp, grid_x1, grid_y1);
          }
        }

        if (best->flip && cell_track != -1) 
        {
          all[i][j]->orient_ = orientMirrorY(orient);
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
            // printf("yeah!\n");
          }
          int x = core_.xMin() + temp->x_;
          int y = core_.yMin() + temp->y_;
          int inst_x, inst_y;
          db_inst_->getLocation(inst_x, inst_y);
          if (x != inst_x || y != inst_y)
            db_inst_->setLocation(x, y);
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
            if (x != inst_x || y != inst_y)
              db_inst_->setLocation(x, y);
          }
          // double hpwl_after = hpwl();
        }
      }
    }
  }
  for(i = 0; i < 1; i ++)
  {
    for(int j = 0; j < 1; j++)
    {
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
    }
    else {
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
