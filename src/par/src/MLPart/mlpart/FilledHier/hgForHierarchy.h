/**************************************************************************
***
*** Copyright (c) 1995-2000 Regents of the University of California,
***               Andrew E. Caldwell, Andrew B. Kahng and Igor L. Markov
*** Copyright (c) 2000-2007 Regents of the University of Michigan,
***               Saurabh N. Adya, Jarrod A. Roy, David A. Papa and
***               Igor L. Markov
***
***  Contact author(s): abk@cs.ucsd.edu, imarkov@umich.edu
***  Original Affiliation:   UCLA, Computer Science Department,
***                          Los Angeles, CA 90095-1596 USA
***
***  Permission is hereby granted, free of charge, to any person obtaining
***  a copy of this software and associated documentation files (the
***  "Software"), to deal in the Software without restriction, including
***  without limitation
***  the rights to use, copy, modify, merge, publish, distribute, sublicense,
***  and/or sell copies of the Software, and to permit persons to whom the
***  Software is furnished to do so, subject to the following conditions:
***
***  The above copyright notice and this permission notice shall be included
***  in all copies or substantial portions of the Software.
***
*** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
*** EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
*** OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
*** IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
*** CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT
*** OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR
*** THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***
***
***************************************************************************/

#ifndef _HGForHIERARCHY_H_
#define _HGForHIERARCHY_H_

#include "HGraph/subHGraph.h"
#include "Ctainers/bitBoard.h"
#include "fillHier.h"

class HGraphForHierarchy : public SubHGraph {
        // Mateus@180515 - Removed static declaration
        BitBoard _madeEdge;
        std::vector<unsigned> _clusteredDegree;
        //--------------

       public:
        // children gives the id's of the nodes to populate the HGraph with
        // adjacentEdges is indexed by nodeId.  For each node, it gives
        // the id's of the adjacent edges.  Note that the nodeIds are
        // not contiguous.  maxEdgeId is the highest edge Id in
        // adjacentEdges
        // Mateus@180515 - Moved the implementation to .h file
        HGraphForHierarchy(const std::vector<unsigned>& oNodes, unsigned numTerminals, const FillableHierarchy& fillH) : _madeEdge(0), SubHGraph(numTerminals, oNodes.size() - numTerminals, fillH.getEdgeWeights().size()) {
                //    _nodeNames = vector<string>(_nodes.size());

                const std::vector<double>& edgeWeights = fillH.getEdgeWeights();
                const std::vector<std::vector<unsigned> >& adjacentEdges = fillH.getAdjacentEdges();
                const std::vector<double>& nodeWeights = fillH.getClusterAreas();

                unsigned n;
                for (n = 0; n < oNodes.size(); n++) {  // similar to the addNode function
                        unsigned oNodeId = oNodes[n];

                        setWeight(n, nodeWeights[oNodeId]);

                        char* nName = new char[strlen(fillH.getNodeName(oNodes[n])) + strlen("-FillHDup") + 2];
                        sprintf(nName, "%s-FillHDup", fillH.getNodeName(oNodes[n]));
                        //    	    _nodeNames[n]     = nName;
                        //    	    _nodeNamesMap[nName]  = n;

                        origNodeToNew[oNodeId] = n;
                        newNodeToOrig[n] = oNodeId;
                }

                // if the size is correct, this just calls clear. Otherwise,
                // it allocates the correct amount of space 1st
                _madeEdge.reset(edgeWeights.size());

                if (_clusteredDegree.size() < edgeWeights.size())
                        _clusteredDegree = std::vector<unsigned>(edgeWeights.size(), 0);
                else
                        std::fill(_clusteredDegree.begin(), _clusteredDegree.end(), 0);

                // count the edge degree, so we can exclude degree 1 edges
                for (n = 0; n < oNodes.size(); n++) {
                        unsigned oNodeId = oNodes[n];
                        for (unsigned e = 0; e < adjacentEdges[oNodeId].size(); e++) _clusteredDegree[adjacentEdges[oNodeId][e]]++;
                }

                for (n = 0; n < oNodes.size(); n++) {
                        unsigned oNodeId = oNodes[n];
                        const HGFNode& node = *_nodes[n];

                        for (unsigned e = 0; e < adjacentEdges[oNodeId].size(); e++) {
                                unsigned eId = adjacentEdges[oNodeId][e];
                                if (_clusteredDegree[eId] < 2) continue;

                                if (!_madeEdge.isBitSet(eId)) {
                                        _madeEdge.setBit(eId);
                                        HGFEdge* newEdge = addEdge(edgeWeights[eId]);

                                        origEdgeToNew[eId] = newEdge->getIndex();
                                        if (newEdgeToOrig)
                                                (*newEdgeToOrig)[newEdge->getIndex()] = eId;
                                        else
                                                abkfatal(0,
                                                         "Filled heirarchy "
                                                         "must have a "
                                                         "newEdgeToOrig, and "
                                                         "hence a net bound.");
                                }

                                addSrcSnk(node, getNewEdgeByOrigIdx(eId));
                        }
                }

                finalize();
        }
};

#endif
