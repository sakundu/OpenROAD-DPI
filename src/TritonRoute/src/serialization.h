/* Authors: Matt Liberty */
/*
 * Copyright (c) 2020, The Regents of the University of California
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the University nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#pragma once

#include <boost/archive/binary_iarchive.hpp>
#include <boost/archive/binary_oarchive.hpp>
#include <boost/serialization/list.hpp>
#include <boost/serialization/map.hpp>
#include <boost/serialization/set.hpp>
#include <boost/serialization/split_member.hpp>
#include <boost/serialization/unique_ptr.hpp>
#include <boost/serialization/vector.hpp>
#include <boost/serialization/weak_ptr.hpp>

namespace fr {

template <class Archive>
bool is_loading(const Archive& ar);

}

#include "db/obj/frShape.h"
#include "db/tech/frConstraint.h"
#include "global.h"

namespace boost::serialization {

// Enable serialization of a std::tuple using recursive templates.
// For some reason boost serialize seems to leave out this std class.
template <uint N>
struct TupleSerializer
{
  template <class Archive, typename... Types>
  static void serialize(Archive& ar,
                        std::tuple<Types...>& t,
                        const unsigned int version)
  {
    (ar) & std::get<N - 1>(t);
    TupleSerializer<N - 1>::serialize(ar, t, version);
  }
};

template <>
struct TupleSerializer<0>
{
  template <class Archive, typename... Types>
  static void serialize(Archive& /* ar */,
                        std::tuple<Types...>& /* t */,
                        const unsigned int /* version */)
  {
  }
};

template <class Archive, typename... Types>
void serialize(Archive& ar, std::tuple<Types...>& t, const unsigned int version)
{
  TupleSerializer<sizeof...(Types)>::serialize(ar, t, version);
}

}  // namespace boost::serialization

namespace fr {

template <class Archive>
void register_types(Archive& ar)
{
  // The serialization library needs to be told about these classes
  // as we often only encounter them through their base classes.
  // More details here
  // https://www.boost.org/doc/libs/1_76_0/libs/serialization/doc/serialization.html#derivedpointers

  ar.template register_type<frRect>();
  ar.template register_type<frPathSeg>();
  ar.template register_type<frPatchWire>();
  ar.template register_type<frPolygon>();

  ar.template register_type<frLef58CutClassConstraint>();
  ar.template register_type<frRecheckConstraint>();
  ar.template register_type<frShortConstraint>();
  ar.template register_type<frNonSufficientMetalConstraint>();
  ar.template register_type<frOffGridConstraint>();
  ar.template register_type<frMinEnclosedAreaConstraint>();
  ar.template register_type<frLef58MinStepConstraint>();
  ar.template register_type<frMinStepConstraint>();
  ar.template register_type<frMinimumcutConstraint>();
  ar.template register_type<frAreaConstraint>();
  ar.template register_type<frMinWidthConstraint>();
  ar.template register_type<
      frLef58SpacingEndOfLineWithinEncloseCutConstraint>();
  ar.template register_type<frLef58SpacingEndOfLineWithinEndToEndConstraint>();
  ar.template register_type<
      frLef58SpacingEndOfLineWithinParallelEdgeConstraint>();
  ar.template register_type<
      frLef58SpacingEndOfLineWithinMaxMinLengthConstraint>();
  ar.template register_type<frLef58SpacingEndOfLineWithinConstraint>();
  ar.template register_type<frLef58SpacingEndOfLineConstraint>();
  ar.template register_type<frLef58CornerSpacingSpacingConstraint>();
  ar.template register_type<frSpacingConstraint>();
  ar.template register_type<frSpacingSamenetConstraint>();
  ar.template register_type<frSpacingTableInfluenceConstraint>();
  ar.template register_type<frSpacingEndOfLineConstraint>();
  ar.template register_type<frLef58CutSpacingTableLayerConstraint>();
  ar.template register_type<frLef58CutSpacingTablePrlConstraint>();
  ar.template register_type<frLef58CutSpacingTableConstraint>();
  ar.template register_type<frSpacingTablePrlConstraint>();
  ar.template register_type<frSpacingTableTwConstraint>();
  ar.template register_type<frSpacingTableConstraint>();
  ar.template register_type<frLef58SpacingTableConstraint>();
  ar.template register_type<frCutSpacingConstraint>();
  ar.template register_type<frLef58CutSpacingConstraint>();
  ar.template register_type<frLef58CornerSpacingConstraint>();
  ar.template register_type<frLef58CornerSpacingSpacingConstraint>();
  ar.template register_type<frLef58CornerSpacingSpacing1DConstraint>();
  ar.template register_type<frLef58CornerSpacingSpacing2DConstraint>();
  ar.template register_type<frLef58RectOnlyConstraint>();
  ar.template register_type<frLef58RightWayOnGridOnlyConstraint>();
}

template <class Archive>
void serialize_globals(Archive& ar)
{
  (ar) & GUIDE_FILE;
  (ar) & OUTGUIDE_FILE;
  (ar) & DBPROCESSNODE;
  (ar) & OUT_MAZE_FILE;
  (ar) & DRC_RPT_FILE;
  (ar) & CMAP_FILE;
  (ar) & OR_SEED;
  (ar) & OR_K;
  (ar) & MAX_THREADS;
  (ar) & BATCHSIZE;
  (ar) & BATCHSIZETA;
  (ar) & MTSAFEDIST;
  (ar) & DRCSAFEDIST;
  (ar) & VERBOSE;
  (ar) & BOTTOM_ROUTING_LAYER_NAME;
  (ar) & TOP_ROUTING_LAYER_NAME;
  (ar) & BOTTOM_ROUTING_LAYER;
  (ar) & TOP_ROUTING_LAYER;
  (ar) & ALLOW_PIN_AS_FEEDTHROUGH;
  (ar) & USENONPREFTRACKS;
  (ar) & USEMINSPACING_OBS;
  (ar) & ENABLE_BOUNDARY_MAR_FIX;
  (ar) & ENABLE_VIA_GEN;
  (ar) & VIAINPIN_BOTTOMLAYERNUM;
  (ar) & VIAINPIN_TOPLAYERNUM;
  (ar) & VIA_ACCESS_LAYERNUM;
  (ar) & MINNUMACCESSPOINT_MACROCELLPIN;
  (ar) & MINNUMACCESSPOINT_STDCELLPIN;
  (ar) & ACCESS_PATTERN_END_ITERATION_NUM;
  (ar) & END_ITERATION;
  (ar) & NDR_NETS_RIPUP_THRESH;
  (ar) & AUTO_TAPER_NDR_NETS;
  (ar) & TAPERBOX_RADIUS;
  (ar) & TAVIACOST;
  (ar) & TAPINCOST;
  (ar) & TAALIGNCOST;
  (ar) & TADRCCOST;
  (ar) & TASHAPEBLOATWIDTH;
  (ar) & VIACOST;
  (ar) & GRIDCOST;
  (ar) & FIXEDSHAPECOST;
  (ar) & ROUTESHAPECOST;
  (ar) & MARKERCOST;
  (ar) & MARKERBLOATWIDTH;
  (ar) & BLOCKCOST;
  (ar) & GUIDECOST;
  (ar) & MARKERDECAY;
  (ar) & SHAPEBLOATWIDTH;
  (ar) & MISALIGNMENTCOST;
  (ar) & HISTCOST;
  (ar) & CONGCOST;
}

// Avoids the need to split the whole serializer like
// BOOST_SERIALIZATION_SPLIT_MEMBER while still allowing for read/write
// specific code.
template <class Archive>
inline bool is_loading(const Archive& ar)
{
  return std::is_same<typename Archive::is_loading, boost::mpl::true_>::value;
}

}  // namespace fr
