
--How to define a wrapped Fukaya cateogry
--Choose an integer n.
--We will be working in (S^1)^n.
--rays will be a set of n-tuples (integers vectors).  
--need not be primitive.
--
--Helper functions
--
--
isFullRank = M-> (rank M == min(rank source M, rank target M))
--
--

isFullRank matrix{{1,0},{0,1}}
isFullRank matrix{{1,0}}
isFullRank transpose matrix{{1,0}}
isFullRank matrix{{1,0},{-1,0}}


WrappedFukaya = new Type of HashTable
WrappedFukaya.synonym = "a toric wrapped Fukaya category"
wrappedFukaya  = method(TypicalValue => WrappedFukaya, Options => true)

wrappedFukaya(List, HashTable) := (A,B) -> (
  new WrappedFukaya from {
    symbol fukayaRays => A,
    symbol hair => B,
    symbol cache => new CacheTable})


wrappedFukaya(List) := (A) -> (
  new WrappedFukaya from {
    symbol fukayaRays => A,
    symbol hair => new HashTable from {},
    symbol cache => new CacheTable})


--hair is going to be represented as (pt, set of rays)
--
hirzebruchRays = {{1,0},{0,1},{-1,3},{0,-1}}
--Make this into a hashtable with keys i corresponding to number
--of rays??

hirzebruchHair = new HashTable from{
    1 => {
	{(0,0), {0}}, 
	{(0,0), {1}}, 
	{(0,0), {2}}, 
	{(0,0), {3}}
	},
    2 => {
	{(0,0), {0,1}}, 
       	{(0,0), {0,2}}, 
	{(0,0), {1,2}}, 
	{(0,0), {0,3}}, 
	{(0,0), {2,3}}
	}
    }

hirzebruchFukaya = wrappedFukaya(hirzebruchRays,hirzebruchHair)
hirzebruchFukaya#hair#2#3
hirzebruchFukaya#fukayaRays#0
hirzebruchFukaya#fukayaRays#3

--rays and hair for the P(1,1,3) for the same set of rays.
weightedRays = {{1,0},{0,1},{-1,3},{0,-1}}
weightedHair = new HashTable from{
    1 => {
	{(0,0), {0}}, 
	--{(0,0), {1}}, we blow down this ray so it disappers from hair, right?
	{(0,0), {2}}, 
	{(0,0), {3}}
	},
    2 => {
	--{(0,0), {0,1}}, 
       	{(0,0), {0,2}},
	--this is the ZZ/3 possibil
	{(0,1/3), {0,2}},
	{(0,2/3), {0,2}},
	--{(0,0), {1,2}}, 
	{(0,0), {0,3}}, 
	{(0,0), {2,3}}
	}
    }


weightedFukaya = wrappedFukaya(weightedRays,weightedHair)

--Input:  set of fukayaRays
--Output:  a hash table with keys = dimension
--         and outputs are lists of chambers of that dimension.

needsPackage "HHLResolutions"
--Input:  set of a rays
--Output:  a hash table with keys dimension 0, ..., dim
--         and values for dim d is the set of faces of dim d in the stratified torus
torusStrata = raySets ->(
    matRays := matrix raySets;
    mhp := makeHHLPolytopes(matSigma, ZZ^2);
    mhpFacesNonUnique := flatten apply(mhp#0,P-> (
    	    V = vertices P;
    	    apply(flatten values faces P, F -> V_(F#0) )
    	    ));
    cellsUnsorted := apply(unique apply(mhpFacesNonUnique, F->(
		F_(sortColumns F))), C-> convexHull C);
    partition(dim,cellsUnsorted)  	
    )
torusStrata(raySets)



raySets = hirzebruchFukaya#fukayaRays
matRays = matrix hirzebruchFukaya#fukayaRays
mhp = makeHHLPolytopes(matSigma, ZZ^2)
mhpFacesNonUnique = flatten apply(mhp#0,P-> (
    V = vertices P;
    apply(flatten values faces P, F -> V_(F#0) )
    )
)
F = mhpFacesNonUnique#11
sortColumns F
cellsUnsorted = apply(unique apply(mhpFacesNonUnique, F-> F_(sortColumns F)), C-> convexHull C)
jaysCells = partition(dim,cellsUnsorted)
#(jaysCells#0)
#(jaysCells#1)
#(jaysCells#2)

--

netList hirzebruchFukaya#fukayaRays
netList(hirzebruchFukaya#hair#1)
netList(hirzebruchFukaya#hair#2)
netList weightedFukaya#fukayaRays
netList(weightedFukaya#hair#1)
netList(weightedFukaya#hair#2)



--WELL DEFINEDNESS IS A MAJOR ISSUE

legalRaySets = new HashTable from
    apply(toList(1..n), i->(
	     i => select(subsets(#sigma,i), C->(
		    rank matrix sigma_C == i
		    ))
	    ))

A = sigma
B = legalRaySets

WF = wrappedFukaya(A,B)
WF#fukayaRays
WF#hair

legalRaySets#1
netList legalRaySets#2

--Our "hair data" should be a subcollection of this,
--corresopnding to the legalRaySets where have hair.


    subsets({1,2,3},1)
--NB: these are the rays of the fan of the corresponding toric variety
--these are also the normal vectors of the hyperplans for the stratification
--
--Where is the potential "higher codim" hair?
--Location of hair is a tuple of h-planes.
needsPackage "HHLResolutions"
matSigma = matrix sigma
mhp = makeHHLPolytopes(matSigma, ZZ^2)
netList apply(mhp#0,i-> faces i)


--


--Jay's hacky way to select the dim 1 or 2 faces (with dan's bad version)
jaysHackySelectFaces = L->(
    apply(join apply((1..2),j-> (L)#j),ell -> ell#0)
    )
jaysHackySelectFaces

apply(join apply((1..2),j-> (faces mhp#0#1)#j),ell -> ell#0)

allTheFaces = apply(mhp#0,i->( jaysHackySelectFaces faces i))
	
	
	select(faces i, F -> #F>
--The first term of this tuple is all maximal cells in
--the stratified torus.
#(mhp#0)
apply(mhp#0, i-> vertices i )
--
--NB:  issues with duplication to be dealt with later.
--
P = mhp#0#1
vertices P
faces P
--we want the faces of codimension of at least 1 and at most n.
legalFaces  

apply(mhp#0, i-> faces i )
