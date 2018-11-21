
range booleanValues = 0..1;

// Input

tuple TAdjTypes {
  key string value;
};

tuple TGroupAdjacencies {
  string grp1Id;
  string grp2Id;
  string adjType;
};

tuple TGroupFacingLimits {
  string grp;
  int minFacings;
  int maxFacings;
};

tuple TGroups {
  key string id;
  int level;
  string parentGroup;
  float alpha;
  float beta;
  int needRectangularity;
  int needSquareness;
};

tuple TGroupsReqdOnShelves {
  key string grp;
  key string shelf;
};

tuple TParameters {
  key float MinTargetAvgDisplayPrice;
  key float MaxTargetAvgDisplayPrice;
};

tuple TSKUShelves {
  key string sku;
  key string shelf;
  int unitsPerFacing;
};

tuple TSKUs {
  key string id;
  int minFacings;
  int maxFacings;
  float demand;
  int replenishRate;
  string parentGroup;
  float width;
  float price;
};

tuple TShelves {
  key string id;
  float width;
  int level;
  float offSet;
};

tuple TWeights {
    float expectedSales;
    float emptySpacePenalty;
    float shortagePenalty;
    float rectangularityPenalty;
    float squarenessPenalty;
    float avgDisplayPricePenalty;
}
{TAdjTypes} AdjTypes = ...;
{TGroupAdjacencies} GroupAdjacencies = ...;
{TGroupFacingLimits} GroupFacingLimits = ...;
{TGroups} Groups with needRectangularity in booleanValues, needSquareness in booleanValues = ...;
{TGroupsReqdOnShelves} GroupsReqdOnShelves = ...;
{TParameters} Parameters = ...;
{TSKUShelves} SKUShelves = ...;
{TSKUs} SKUs = ...;
{TShelves} Shelves = ...;
{TWeights} Weights = ...;

TParameters Parameter = first(Parameters);
TWeights Weight = first(Weights);


dvar int numFacingsSKUOnShelf [SKUShelves];
dvar float offsetSKUOnShelf [SKUShelves];


sorted {int} Levels = {g.level | g in Groups};
{TGroups} GroupsForLevel[l in Levels] = {<i,l,p,a,b,nr,ns> | <i,l,p,a,b,nr,ns> in Groups};
 
{string} GroupIDs = { g.id | g in Groups };
assert forall(g in Groups) g.id in GroupIDs;
assert card(Groups) == card(GroupIDs);
 
TGroups GroupForID[GroupIDs] = [g.id : g | g in Groups];
{TGroups} FirstLevelGroups = {g| g in GroupsForLevel[first(Levels)]};
{TGroups} SquareGroups = {g | g in Groups : g.needSquareness == 1};
{TGroups} GroupsWithSpaceElasticity = {g | g in Groups : g.alpha >= 0 && g.beta >= 0};
 
//All Groups with space elasticiy should be at same level
assert card({g.level | g in GroupsWithSpaceElasticity}) == 1;
 
//Make sure level of parentGroup for a group is one level higher
assert forall(l in Levels : l != last(Levels), g in GroupsForLevel[l]) GroupForID[g.parentGroup].level == next(Levels, l); 
 
//Make sure there is at least one grouping of SKUs
assert card(Groups) >= 1;

{string} SKUIDs = { sku.id | sku in SKUs };
assert forall(s in SKUs) s.id in SKUIDs;
assert card(SKUs) == card(SKUIDs);
 
TSKUs SKUForID[SKUIDs] = [s.id : s | s in SKUs];
 
//Make sure that Min/Max facings is >=0
assert forall(s in SKUs) (s.minFacings >= 0) && (s.maxFacings >= 0);
 
{string} SKUsForGroup[GroupIDs];

execute POPULATE_SKUS_FOR_GROUPS {
  	for(var i=0; i<Levels.size; i++) {
  		var level = Opl.item(Levels, i);

  		for(var g=0; g<GroupsForLevel[level].size; g++) { 
  			var group = Opl.item(GroupsForLevel[level], g);
  		
	  		if(i==0) {//first level (levels are sorted in ascending order)
	  			for(var s=0; s<SKUs.size; s++) {
	  				var sku = Opl.item(SKUs, s);
	  				
	  				if(sku.parentGroup == group.id) {
	  					SKUsForGroup[group.id].add(sku.id);
	  				}
	  			}
	  		}
	  		else {//higher level
	  			var lowerLevel = Opl.prev(Levels, level);

	  			for(var lg=0; lg<GroupsForLevel[lowerLevel].size; lg++) {
	  				var lowerGroup = Opl.item(GroupsForLevel[lowerLevel], lg);

	  				//loop over SKUs of lower group and add to group if group is a parent of lower group
	  				if(lowerGroup.parentGroup == group.id) {
	  					//writeln("Child Group for Grp: ", group.id, " is: ", lowerGroup.id);
	  					for(var ls=0; ls<SKUsForGroup[lowerGroup.id].size; ls++) {
	  						var l_sku = Opl.item(SKUsForGroup[lowerGroup.id], ls);
	  						SKUsForGroup[group.id].add(l_sku);
	  					}
	  					
	  				}//end-if group is a parent of lower group
	  			}
	  		}
	  		
	  	}//end looping over groups for level
  	}//end looping over levels

  };
 
 
//Max Facings for the groups with space-elasticity
int MaxFacings[g in GroupsWithSpaceElasticity] = sum(s in SKUsForGroup[g.id]) SKUForID[s].maxFacings;
 
{string} ShelfIDs = { s.id | s in Shelves };
assert forall(s in Shelves) s.id in ShelfIDs;
assert card(Shelves) == card(ShelfIDs);
 
TShelves ShelfForID[ShelfIDs] = [s.id : s | s in Shelves];
 
sorted {int} RowLevels = {rl | <i,w,rl,o> in Shelves};
int MaxRowLevel = last(RowLevels);
 
 
tuple SKUGroupShelf {
 	TGroups grp;
 	TShelves shelf;
};
 
{SKUGroupShelf} GroupShelves = {<g,ShelfForID[sh]> | g in Groups, sk in SKUsForGroup[g.id], <sk,sh,u> in SKUShelves};
{SKUGroupShelf} RectangularGroupShelves = {g | g in GroupShelves : g.grp.needRectangularity == 1};
 
tuple SKUGroupShelfPair {
 	string grp;
 	string shelf1;
 	string shelf2;
}
 
{SKUGroupShelfPair} GroupAdjacentShelves = {<g.id,s1.id,s2.id> | <g,s1> in GroupShelves, <g,s2> in GroupShelves : s2.level == s1.level + 1}; 
 
 
//Groups with adjacency should be at same level
assert forall(<g1,g2,a> in GroupAdjacencies) (GroupForID[g1].level == GroupForID[g2].level);
 
{TGroups} GroupsWithLeftAdjacency[l in Levels] = {GroupForID[g1] | <g1,g2,"Left"> in GroupAdjacencies : GroupForID[g1].level == l} 
 													union {GroupForID[g2] | <g1,g2,"Left"> in GroupAdjacencies : GroupForID[g2].level == l};
{TGroups} OrderedGroupsForLevel[l in Levels] = GroupsWithLeftAdjacency[l] union (GroupsForLevel[l] diff GroupsWithLeftAdjacency[l]);
 
//{SKUGroupAdjacency} GroupLeftAdjacencies = {<g1,g2,"Left"> | <g1,g2,"Left"> in GroupAdjacencies};
{TGroupAdjacencies} GroupTopAdjacencies = {<g1,g2,"Top"> | <g1,g2,"Top"> in GroupAdjacencies};
 
{string} GroupsAbove = {g1 | <g1,g2,a> in GroupTopAdjacencies};
{string} GroupsBelow = {g2 | <g1,g2,a> in GroupTopAdjacencies};

execute CPLEX_PARAM {
   	cplex.tilim = 180;
  	cplex.clocktype = 2;//wall clock time
  	cplex.rinsheur = 50;
};

//dvar int+ numFacingsSKUOnShelf[<sk,sh,u> in SKUShelves] in SKUForID[sk].minFacings..SKUForID[sk].maxFacings;
 
dvar boolean isGroupOnShelf[GroupShelves];
dvar boolean isSKUOnShelf[SKUShelves];

dvar float+ offsetGroupOnShelf[<g,s> in GroupShelves] in s.offSet..(s.offSet+s.width);
 
dvar boolean isGroupOnAdjShelf[GroupAdjacentShelves];
dvar int unitsShortageVar[SKUs];
dvar float+ emptySpaceOnShelfVar[Shelves];
  
//adjacency variables
dvar int+ lowestShelfForGroup[GroupsAbove];
dvar int+ highestShelfForGroup[GroupsBelow];
 
//slack variables
dvar float+ squareShapeSlack[SquareGroups]; 
dvar float+ rectShapeLeftSlack[RectangularGroupShelves];
dvar float+ rectShapeRtSlack[RectangularGroupShelves];
 
dvar float+ minAvgTargetPriceSlack;
dvar float+ maxAvgTargetPriceSlack;
 
dvar int+ numFacingsGroupOnShelf[GroupShelves];
dvar float+ allocWidthGroupOnShelf[GroupShelves];

dvar int numFacingsGroup[g in Groups];

dexpr int numRowLevelsGroup[g in Groups] = sum(<g,s> in GroupShelves) isGroupOnShelf[<g,s>];
 
dexpr int numFacingsSKU[sk in SKUs] = sum(<sk.id,sh,u> in SKUShelves) numFacingsSKUOnShelf[<sk.id,sh,u>];
 
dvar float es;
dexpr float expectedSales = es;//sum(g in GroupsWithSpaceElasticity) piecewise(i in 1..MaxFacings[g]) 
 							//		{GroupForID[g].alpha*(pow(i,GroupForID[g].beta) - pow(i-1,GroupForID[g].beta))->i; 0} (0,0) numFacingsGroup[g];
 
dexpr float emptySpacePenalty = sum(s in Shelves) emptySpaceOnShelfVar[s]; 
dexpr float shortagePenalty = sum(s in SKUs) unitsShortageVar[s]; 
dexpr float rectangularityPenalty = sum(<g,s> in RectangularGroupShelves) (rectShapeLeftSlack[<g,s>] + rectShapeRtSlack[<g,s>]); 
dexpr float squarenessPenalty = sum(g in SquareGroups) squareShapeSlack[g]; 
dexpr float avgDisplayPricePenalty = minAvgTargetPriceSlack + maxAvgTargetPriceSlack;
 
maximize Weight.expectedSales * expectedSales
		- Weight.emptySpacePenalty * emptySpacePenalty
 		- Weight.shortagePenalty * shortagePenalty 
 		- Weight.rectangularityPenalty * rectangularityPenalty  
 		- Weight.squarenessPenalty * squarenessPenalty    
 		- Weight.avgDisplayPricePenalty * avgDisplayPricePenalty;
 		
 
 constraints {
   forall(g in Groups)
     numFacingsGroup[g] == sum(sk in SKUsForGroup[g.id], <sk,sh,u> in SKUShelves) numFacingsSKUOnShelf[<sk,sh>];

//    es == 5;
 
 	es == sum(g in GroupsWithSpaceElasticity) piecewise(i in 1..MaxFacings[g]) 
 									{g.alpha*(pow(i,g.beta) - pow(i-1,g.beta))->i; 0} (0,0) numFacingsGroup[g];
 
 	forall(<g,sh> in GroupShelves) {
 		numFacingsGroupOnShelf[<g,sh>] == sum(sk in SKUsForGroup[g.id], 
 		                            <sk,sh.id,u> in SKUShelves) numFacingsSKUOnShelf[<sk,sh.id>];
 		allocWidthGroupOnShelf[<g,sh>] == sum(sk in SKUsForGroup[g.id], <sk,sh.id,u> in SKUShelves) (SKUForID[sk].width * numFacingsSKUOnShelf[<sk,sh.id>]);
 	}
 
 	//relate isSKUOnShelf, offsetSKUOnShelf and numFacingsSKUOnShelf
 	forall(<sk,sh,u> in SKUShelves) {
 		numFacingsSKUOnShelf[<sk,sh>] <= ceil(ShelfForID[sh].width/SKUForID[sk].width) * isSKUOnShelf[<sk,sh>];
 		numFacingsSKUOnShelf[<sk,sh>] >= 0.5 * isSKUOnShelf[<sk,sh>];
 		offsetSKUOnShelf[<sk,sh>] + SKUForID[sk].width * numFacingsSKUOnShelf[<sk,sh>] <= ShelfForID[sh].offSet + ShelfForID[sh].width;
 	}
	
 	//relate isGroupOnShelf and isSKUOnShelf
 	forall(<g,s> in GroupShelves) {
 		isGroupOnShelf[<g,s>] <= sum(sk in SKUsForGroup[g.id]) isSKUOnShelf[<sk,s.id>];
 		card(SKUsForGroup[g.id]) * isGroupOnShelf[<g,s>] >= sum(sk in SKUsForGroup[g.id]) isSKUOnShelf[<sk,s.id>];
 	}
 	
 	//If a group at lower level is on shelf then its parent group should also be on shelf
 	forall(l in (Levels diff {first(Levels)}), g in GroupsForLevel[l], <g,s> in GroupShelves) {
 		isGroupOnShelf[<g,s>] <= sum(gc in GroupsForLevel[prev(Levels, l)] : gc.parentGroup == g.id) isGroupOnShelf[<gc,s>];
 		(sum(gc in GroupsForLevel[prev(Levels, l)] : gc.parentGroup == g.id) 1) * isGroupOnShelf[<g,s>] 
 									>= sum(gc in GroupsForLevel[prev(Levels, l)] : gc.parentGroup == g.id) isGroupOnShelf[<gc,s>];
 	}
 	
 	//relate SKU Group shelf-adjacency vars
 	forall(<g,s1,s2> in GroupAdjacentShelves) {
 		2 * isGroupOnAdjShelf[<g,s1,s2>] <= isGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + isGroupOnShelf[<GroupForID[g],ShelfForID[s2]>];
 		isGroupOnAdjShelf[<g,s1,s2>] >= isGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + isGroupOnShelf[<GroupForID[g],ShelfForID[s2]>] - 1;
 	}

 	//SKU Group contiguity
 	forall(g in GroupIDs) {
// 		(sum(<g,s1,s2> in GroupAdjacentShelves) isGroupOnAdjShelf[<g,s1,s2>] ) >= (sum(<g,s> in GroupShelves) isGroupOnShelf[<g,s>] - 1);
 		(sum(gas in GroupAdjacentShelves: gas.grp==g) isGroupOnAdjShelf[gas] ) >= (sum(gs in GroupShelves: gs.grp.id==g) isGroupOnShelf[gs] - 1);
 	}
	
 	//SKU on single shelf
 	forall(s in SKUIDs) {
 		sum(<s,sh,u> in SKUShelves) isSKUOnShelf[<s,sh>] <= 1;
 	}

 	//Max facings on a shelf
 	forall(sh in ShelfIDs) {
 		sum(<sk,sh,u> in SKUShelves) (SKUForID[sk].width * numFacingsSKUOnShelf[<sk,sh>]) <= ShelfForID[sh].width;
 		sum(<sk,sh,u> in SKUShelves) (SKUForID[sk].width * numFacingsSKUOnShelf[<sk,sh>]) + emptySpaceOnShelfVar[ShelfForID[sh]] == ShelfForID[sh].width;
 	}
	
 	//relate units shortage
 	forall(s in SKUIDs) {
 		sum(<s,sh,u> in SKUShelves) u * numFacingsSKUOnShelf[<s,sh>] + unitsShortageVar[SKUForID[s]] 
 		                                  >= SKUForID[s].demand * SKUForID[s].replenishRate;
 	}
 	
 	//relate slacks for rectangularity
 	forall(<g,s1,s2> in GroupAdjacentShelves : GroupForID[g].needRectangularity == 1) {
 		offsetGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + rectShapeLeftSlack[<GroupForID[g],ShelfForID[s1]>]
 		                                 >= offsetGroupOnShelf[<GroupForID[g],ShelfForID[s2]>] + rectShapeLeftSlack[<GroupForID[g],ShelfForID[s2]>]
 										- maxl(ShelfForID[s1].offSet+ShelfForID[s1].width, ShelfForID[s2].offSet+ShelfForID[s2].width) * (1 - isGroupOnAdjShelf[<g,s1,s2>]);

 		
 		offsetGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + rectShapeLeftSlack[<GroupForID[g],ShelfForID[s1]>] <= offsetGroupOnShelf[<GroupForID[g],ShelfForID[s2]>] + rectShapeLeftSlack[<GroupForID[g],ShelfForID[s2]>]
 										+ maxl(ShelfForID[s1].offSet+ShelfForID[s1].width, ShelfForID[s2].offSet+ShelfForID[s2].width) * (1 - isGroupOnAdjShelf[<g,s1,s2>]);
 										
 		numFacingsGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + rectShapeRtSlack[<GroupForID[g],ShelfForID[s1]>] >= numFacingsGroupOnShelf[<GroupForID[g],ShelfForID[s2]>] + rectShapeRtSlack[<GroupForID[g],ShelfForID[s2]>]
 										- maxl(ShelfForID[s1].offSet+ShelfForID[s1].width, ShelfForID[s2].offSet+ShelfForID[s2].width) * (1 - isGroupOnAdjShelf[<g,s1,s2>]);
 										
 		numFacingsGroupOnShelf[<GroupForID[g],ShelfForID[s1]>] + rectShapeRtSlack[<GroupForID[g],ShelfForID[s1]>] <= numFacingsGroupOnShelf[<GroupForID[g],ShelfForID[s2]>] + rectShapeRtSlack[<GroupForID[g],ShelfForID[s2]>]
 										+ maxl(ShelfForID[s1].offSet+ShelfForID[s1].width, ShelfForID[s2].offSet+ShelfForID[s2].width) * (1 - isGroupOnAdjShelf[<g,s1,s2>]);
 	}

 	//relate slacks for squareness
 	forall(<g,s> in GroupShelves : g.needSquareness == 1) {
 		//numFacingsGroupOnShelf[<g,s>] <= squareShapeSlack[g] + numRowLevelsGroup[g];
 		numFacingsGroupOnShelf[<g,s>] >= numRowLevelsGroup[g] - squareShapeSlack[g];
 		//numRowLevelsGroup[g] <= squareShapeSlack[g] + numFacingsGroupOnShelf[<g,s>] + MaxRowLevel * (1 - isGroupOnShelf[<g,s>]);
 		numRowLevelsGroup[g] >= numFacingsGroupOnShelf[<g,s>] - squareShapeSlack[g];
 	}
 	
 	//placement order among the groups for each level
 	forall(l in Levels, g in (OrderedGroupsForLevel[l] diff {last(OrderedGroupsForLevel[l])}), <g,s> in GroupShelves : 
 																	<next(OrderedGroupsForLevel[l], g), s> in GroupShelves) {
 		offsetGroupOnShelf[<g,s>] + allocWidthGroupOnShelf[<g,s>] <= offsetGroupOnShelf[<next(OrderedGroupsForLevel[l], g), s>];
 	}
 	
 	//placement order among SKUs of group at level-1
 	forall(g in GroupsForLevel[first(Levels)], s in (SKUsForGroup[g.id] diff {last(SKUsForGroup[g.id])}), <s,sh,u> in SKUShelves :
 																	<next(SKUsForGroup[g.id], s),sh,u> in SKUShelves) {
 		offsetSKUOnShelf[<s,sh>] + SKUForID[s].width * numFacingsSKUOnShelf[<s,sh>] <= 
 					offsetSKUOnShelf[<next(SKUsForGroup[g.id], s),sh>];
 	}
 	
 	//SKUs should be enclosed within level-1 group
 	forall(g in GroupsForLevel[first(Levels)], s in SKUsForGroup[g.id], <s,sh,u> in SKUShelves) {
 		offsetSKUOnShelf[<s,sh>] >= offsetGroupOnShelf[<g,ShelfForID[sh]>];
 		offsetSKUOnShelf[<s,sh>] + SKUForID[s].width * numFacingsSKUOnShelf[<s,sh>] <= 
 		                 offsetGroupOnShelf[<g,ShelfForID[sh]>] + allocWidthGroupOnShelf[<g,ShelfForID[sh]>];
 	}
		
 	//Group at a lower level should be enclosed by group at higher level
 	forall(l in (Levels diff {last(Levels)}), g in GroupsForLevel[l], <g,s> in GroupShelves) {
 		offsetGroupOnShelf[<g,s>] >= offsetGroupOnShelf[<GroupForID[g.parentGroup],s>];
 		offsetGroupOnShelf[<g,s>] + allocWidthGroupOnShelf[<g,s>] <= offsetGroupOnShelf[<GroupForID[g.parentGroup],s>] + allocWidthGroupOnShelf[<GroupForID[g.parentGroup],s>];
 	}
 	
 	//relate lowest shelf for group

 	forall(<g,s> in GroupShelves : g.id in GroupsAbove) {
 		lowestShelfForGroup[g.id] <= s.level * isGroupOnShelf[<g,s>] + 
 		                               (MaxRowLevel + 1) * (1 - isGroupOnShelf[<g,s>]);
 	}
 	
 	//relate highest shelf for group

 	forall(<g,s> in GroupShelves : g.id in GroupsBelow) {
 		highestShelfForGroup[g.id] >= s.level * isGroupOnShelf[<g,s>];
 	}
 	
 	//top-adjacency constraint
 	forall(<g1,g2,a> in GroupTopAdjacencies) {
 		lowestShelfForGroup[g1] >= highestShelfForGroup[g2];
 	}

 	//relate target average display price
 	sum(s in SKUs) s.price * numFacingsSKU[s] >= Parameter.MinTargetAvgDisplayPrice * sum(s in SKUs) numFacingsSKU[s] - minAvgTargetPriceSlack;
 	sum(s in SKUs) s.price * numFacingsSKU[s] <= Parameter.MaxTargetAvgDisplayPrice * sum(s in SKUs) numFacingsSKU[s] + maxAvgTargetPriceSlack;

	//SKU Group required placement on specific shelves
	forall(i in GroupsReqdOnShelves : <GroupForID[i.grp], ShelfForID[i.shelf]> in GroupShelves) {
		reqdPlacement:
		isGroupOnShelf[<GroupForID[i.grp], ShelfForID[i.shelf]>] == 1;
	}

	//Facing Limits for SKU Group
//	
	forall(i in GroupFacingLimits) {
		minFacings:
        numFacingsGroup[GroupForID[i.grp]] >= i.minFacings;
		maxFacings:
		numFacingsGroup[GroupForID[i.grp]] <= i.maxFacings+1;
	}

}
/*




*/


// Output

dexpr float emptySpacePenaltyKPI = sum(s in Shelves) emptySpaceOnShelfVar[s]; 
dexpr float shortagePenaltyKPI = sum(s in SKUs) unitsShortageVar[s]; 
dexpr float rectangularityPenaltyKPI = sum(<g,s> in RectangularGroupShelves) (rectShapeLeftSlack[<g,s>] + rectShapeRtSlack[<g,s>]); 
dexpr float squarenessPenaltyKPI = sum(g in SquareGroups) squareShapeSlack[g]; 
dexpr float avgDisplayPricePenaltyKPI = minAvgTargetPriceSlack + maxAvgTargetPriceSlack;

tuple TEmptySpaceOnShelf {
  key string shelf;
  float value;
};

tuple TGroupFacings {
  key string grp;
  float alpha;
  float beta;
  int numFacings;
};

tuple TGroupOnShelfPlacement {
  key string grp;
  key string shelf;
  int numFacings;
  float offset;
  float widthOnShelf;
};

tuple TResults {
  key float minAvgTargetPriceSlack;
  key float maxAvgTargetPriceSlack;
  key float es;
};

tuple TSKUOnShelfPlacement {
  key string sku;
  key string shelf;
  int numFacings;
  float offset;
  float skuWidth;
  float offset2;
  string parentGrp;
};

tuple TUnitsShortage {
  key string sku;
  float value;
};
{TGroupFacings} GroupFacings;
{TGroupOnShelfPlacement} GroupOnShelfPlacement;
TResults Results;
{TSKUOnShelfPlacement} SKUOnShelfPlacement;
{TEmptySpaceOnShelf} emptySpaceOnShelf;

{TUnitsShortage} unitsShortage;

execute OUTPUT {
	for ( var skuShelf in SKUShelves ) {
		if( isSKUOnShelf[skuShelf] > 0.5 ) {
			SKUOnShelfPlacement.add(skuShelf.sku,
			                         skuShelf.shelf,
			                         numFacingsSKUOnShelf[skuShelf],
			                         offsetSKUOnShelf[skuShelf],
			                         SKUForID[skuShelf.sku].width,
			                         offsetSKUOnShelf[skuShelf] + numFacingsSKUOnShelf[skuShelf]*SKUForID[skuShelf.sku].width,
			                         SKUForID[skuShelf.sku].parentGroup
			                         );
		}
	}
	
	for ( var grp in Groups ) {
	  GroupFacings.add(grp.id, grp.alpha, grp.beta, numFacingsGroup[grp] );	  
	}	
	
	for ( var gs in GroupShelves ) {
	  	if ( isGroupOnShelf[gs] > 0.5 ) {
			GroupOnShelfPlacement.add(gs.grp.id,
		                          gs.shelf.id,
		                          numFacingsGroupOnShelf[gs],
		                          offsetGroupOnShelf[gs],
		                          allocWidthGroupOnShelf[gs]                          
		                        )
 		}		                        
	}
	for ( var sku in SKUs ) {
		unitsShortage.add( sku.id, unitsShortageVar[sku] ); 	
	}
	
	for ( var shelf in Shelves ) {
		emptySpaceOnShelf.add( shelf.id, emptySpaceOnShelfVar[shelf] );  
	}	  				  				    	  
} 
 
