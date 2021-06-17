newPackage(
    "RootReduce",
    Version =>"0.1",
    Date => "October 24, 2019",
    Authors =>{{Name => "Andrew Pitman",
        Email => "apitman@g.clemson.edu"}},
    Headline => "Reduce the number of roots of your polynomial",
    DebuggingMode => false,
    PackageImports => {"Bertini"}
    )

export{"rootReduce",
    "Roots", -- list of points. option to specify roots
    "Sparse" -- boolean. option to maintain sparsity of terms
    }

    -- here we create the method which reduces the number of roots of a polynomial by altering its coefficients
        -- if Sparse is set to true, then rootReduce will return a polynomial with the same set of monomials (with nonzero coefficients) as its input
        -- eventually we will add options to modify the homotopy used in rootReduce
        -- if specified, Roots should be of the form {(r_1,m_1),(r_2,m_2),...,(r_n,m_n)} where r_k is a root and m_k is its multiplicity

    rootReduce = method(Options=>{Sparse=>false,Roots=>null});

    -- rootReduce needs to act on a ring element regardless of the ring, so we only define the method when it acts on some ring element

    rootReduce RingElement := o -> f ->(

        ------------------------------
        -- terminal output function --
        ------------------------------

        -- we will use OUT to write output to stderr, since Mcaulay2 does not do this by default from inside of a method definition
        -- OUT := {Peeking => false, Description => false} >> opt -> (u,v) -> ( stderr << u << " = " << v << endl; if opt.Peeking == true then stderr << "peek: " << peek v << endl; if opt.Description == true then stderr << "description: " << describe v << endl; stderr << endl);

        --------------------------
        -- x: the indeterminate --
        --------------------------

        -- throw an error if f is multivariate or constant
        if #support(f) > 1 then error "f needs to be univariate";
        if #support(f) == 0 then error "f is constant";

        -- get the variable used for f
        x := first support f;

        ----------------
        -- roots of f --
        ----------------

        -- if Roots is specified, we expect it to be a list of points
        yList := {};
        if class o.Roots =!= Nothing then yList = o.Roots

        -- otherwise, get the roots of f at the starting parameters, yielding a list of points
        else yList = bertiniZeroDimSolve({f},AffVariableGroup => {x});

        -- if f already has only one root, return f -- this may need to change when decisions are made about how output should be handled
        if #yList == 1 then return f;

        -- get the multiplicities of the roots and put them in a list
            -- presumably this is unnessary as we can get this information from the points, but I'm writing the code just in case it turns out to be super convenient
        multList := apply(yList, u -> u.Multiplicity); --OUT("multList",multList);

        -- record the number of roots minus 1 (because we will label a 0th root)
        nRoots := #yList - 1; --OUT("nRoots",nRoots);

        -- record number of lagrange multipliers that we will use minus 1
        nLagrange := sum multList + 1;

        ----------------------------
        -- terms and coefficients --
        ----------------------------

        -- get monomials and coefficients of f
            -- if Sparse (option in this method) is set to true, we only get nonzero coefficients and their monomials. Otherwise, we get all possible monomials and coefficients up to the degree of f
        (monomVec, qVec) := coefficients(f, Monomials=> (if o.Sparse == false then apply(first degree f + 1, n-> x^n) else null));

        -- save the number of parameters minus 1 (since we have a parameter 0) to nCoef
        nCoef := numRows qVec - 1;

        -- define p_0 through p_nCoef as symbols within the method (this can be done by defining p as a symbol)
        p := symbol p;

        -- define a ring that includes the support of f along with variables for the coefficients (parameters) of f
        R := CC[x,p_0..p_nCoef];
        use R;

        -- update the monomials to the new ring R
        monomVec = substitute(monomVec,R);

        -- make a list and a vector of the parameters
        pList := toList (p_0..p_nCoef);
        pVec := transpose matrix {pList};

        -- make a new polynomial fp in R which is formed by replacing the coefficients of f with parameters (indeterminates in R)
        fp := (monomVec*pVec)_(0,0);

        -------------------------------------
        -- RHom: the ring for the homotopy --
        -------------------------------------

        r := symbol r;
        l := symbol l;
        timeVar := symbol timeVar;
        pathVar := symbol pathVar;
        -- make a variable for each root in a new ring that we will use for the homotopy
        RHom := CC[ r_0..r_nRoots, p_0..p_nCoef, l_0..l_nLagrange, timeVar, pathVar ];
        use RHom;

        --------------------------------------------------------------
        -- g: the function that ensures that roots reduce in number --
        --------------------------------------------------------------

        -- indices is the sequence of all pairs (i,j) such that 0 <= i < j <= nRoots.
        indicesMaker := (a,b)->apply(a+1..b,u->(a,u));
        indices := splice apply(0..nRoots-1, u->indicesMaker(u,nRoots)); --OUT("indices",indices);
        g := product( indices, (i,j)->(r_i-r_j)) - timeVar*product(indices, (i,j)->(yList#i#Coordinates#0 - yList#j#Coordinates#0) ); --OUT("g",g);

        ----------------------------------------------------------------------------------------
        -- F: the function which ensures root variables remain roots as the parameters change --
        ----------------------------------------------------------------------------------------

        -- make a polynomial fr_k for each root_k, which is just fp but with indeterminate r_k instead of x
        fMap := i -> map(RHom,R,{r_i,p_0..p_nCoef});
        fr := apply(nRoots+1, j -> (fMap j) fp);

        -- multiDiff takes the 0th through nth proper derivative of f with respect to x and puts all of them in a sequence
        multiDiff := (u,v,n) -> sequence(v) | accumulate( (a,b)->diff(b,a), v, n:u ); --OUT("multiDiff(x,x^5+3*x^4+4*x+5,5)",multiDiff(r_0,r_0^5+3*r_0^4+4*r_0+5,5));

        -- F will be directly inserted. It is responsible for making sure that f remains 0 at every root, and that some derivatives of f remain zero at roots of certain multiplicities
        F := splice apply( nRoots+1, i -> ( multiDiff( r_i, fr_i, yList#i#Multiplicity-1 ) ) ); --OUT("F",F);

        ---------------------
        -- H: the homotopy --
        ---------------------

        -- First we form the top of the homotopy
        Htop := transpose( matrix{F} | matrix{{g}} ); --OUT("Htop",Htop);

        -- next we form the middle of the homotopy

        -- LagrangeMat is the matrix whose critical point we'd like to reach
        LagrangeMat := submatrix(jacobian matrix{ F | {g}},{0..nCoef+nRoots+1},);

        -- we have to form the first column, (0, p-q)^T, of the Lagrange matrix and then concatenate it on.
        qVec = substitute(qVec, RHom); --OUT("qVec",qVec);
        LagrangeCol := matrix{{p_0..p_nCoef}} - transpose qVec;
        LagrangeCol = transpose( matrix{{(nRoots+1):0_RHom}} | LagrangeCol );
        LagrangeMat = LagrangeCol | LagrangeMat; --OUT("LagrangeMat",LagrangeMat);

        -- form a vector for the l_k's
        lambdaVec := transpose matrix{{l_0..l_nLagrange}}; --OUT("lambdaVec",lambdaVec);

        -- the middle of the homotopy in matrix form is Hmid
        Hmid := LagrangeMat * lambdaVec; --OUT("Hmid",Hmid);

        -- next we form the bottom of the homotopy
        setRandomSeed currentTime();
        a := matrix{{1_RHom}} | matrix fillMatrix(mutableMatrix(CC,1,nLagrange+1)); --OUT("a",a);
        Hbottom := a*(lambdaVec || matrix{{-1_RHom}}); --OUT("Hbottom",Hbottom);

        -- get the starting value for l_0
        a0 := last first entries a; --OUT("a0",a0);

        -- finally we put the top, middle, and bottom together to get the whole homotopy in matrix form
        Hmatrix := Htop || Hmid || Hbottom; --OUT("Hmatrix",Hmatrix);

        -- convert the homotopy to list form
        H := first entries transpose (Htop || Hmid || Hbottom); --OUT("H",H);
        -- next we form the Bertini Command

        ---------------------
        -- combining roots --
        ---------------------

        -- create a simple list of our starting parameters
        qList := first entries transpose qVec; --OUT("qList",qList);

        -- place the starting system in a variable --r,p,l,a
        -- OUT("yList",yList,Peeking=>true);
        S1 := {apply(yList, u->u#Coordinates),qList,a0,toList(nLagrange:0)};
        S1 = flatten flatten S1;
        --OUT("S1",S1,Peeking=>true);


        -- COMPUTE the actual homotopy
        S0 := bertiniUserHomotopy(pathVar,{timeVar=>pathVar},H,{S1}); --OUT("S0",S0,Peeking=>true);

        ------------
        -- output --
        ------------

        -- output just the numbers associated with the roots
        --OUT("roots",take(S0#0#Coordinates, nRoots+1));

        -- now we need to automatically identify the roots that have combined.

        -- output the new polynomial, its roots, and the bertini output
        use CC[x];
	cS0 := take(S0#0#Coordinates, nRoots+1);
        fS0 := product apply(cS0, multList, (y,z)-> (x - realPart y)^z);
	rS0 := apply(cS0, multList, (y,z)->point {{y},Multiplicity=>z});
        return (fS0,rS0,S0);

        )

beginDocumentation()
multidoc ///
    Node
        Key
            RootReduce
        Headline
            Reduce the number of roots of your polynomial
        Description
            Text
                {\em RootReduce} contains the function {\em rootReduce}.
    Node
        Key
            (rootReduce,RingElement)
            rootReduce
        Headline
             {\em rootReduce} can reduce the number of roots of a univariate polynomial with minimial change to its coefficients.
        Usage
            rootReduce f
        Inputs
            f:
        Outputs
            :
                a polynomial of the same degree as {\tt f}, but with fewer roots
    Node
        Key
            Roots
        Headline
            Optional list of points representing the roots of {\tt f}
        Usage
            Roots => {point{{-1.5},Multiplicity=>2},point{{1.0},Multiplicity=>3}}
        Caveat
            Multiplicity must be specified for each point
    Node
        Key
            Sparse
        Headline
            option to maintain sparsity of terms of {\tt f}. {\tt false} by default.
///

TEST ///
    needsPackage "Bertini"; R = CC[x,y]; rootList = {{-2,1},{-1,1},{1,1},{1.8,1},{2.2,1}}; rootPoints = apply(rootList, z->point{{z#0},Multiplicity=>z#1}); p1 = product apply(rootList, r->(y-r#0)^(r#1)); p2 = rootReduce(p1)
///

end --