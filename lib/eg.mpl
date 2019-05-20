###################################################################
unprotect('EG'):
EG := module ()

    description     "a package implementing a family of EG algorithms to construct embracing systems"
                    "and reveal systems' singularities";
    export
        EG_delta,
        EG_sigma,
        LaurentSolution,
        Singsys,
        RegularSolution,
        FormalSolution,

        # matrix diffop form of the system
        Sys,
        # matrix theta form of the system
        thetaSys,

        theta,
        diff2theta, theta2diff;

global _SingSysShifts;


    local
        `EG_delta/doit`,
        `EG_sigma/doit`,
        `EG_sigma_infinite/doit`,
        ApplyEGseq,
        ComputeRHS,
        Combine,
        dualnormal,
        RegularSolutionComponent,
        Xi,
        MatCoeffs,

        doFormalSolution,
        FormalSolution_diff_form,
        FormalSolution_theta_form,
        doFSforPolyCf,
        convertSysToArray,
        Poincare_rank,
        Katz_invariant,
        ExponentialParts,
        BlockDiagonalization,
        doMoser,
        Lemma2_1;

        dualnormal := e->simplify(radnormal(e),RootOf);

    ###################################################################
    # Singsys - given a differential system, constructs a nonzero polynomial d(x) such that if
    #           the given system has Laurent series solution with in (x-a) for some point a, and
    #           a component of this solution has a nonzero polar part then d(a)=0.
    # The procedure uses the Singsys algorithm, which desingularize the leading matrix of
    # the given system using EG_delta algorithm.
    # The input parameters are the system given as the list of its equations and the list of
    # the corresponding unknown functions. Optionally the third parameter may be also given
    # which is the name of the method to be used in EG_delta ("ordinary", "random", "zero").
    ###################################################################

    Singsys := proc(sys, vars)
        local d, d1, M, s, method, n;

        if nargs=3 and type(args[3],string) then
            method:=args[3]
        else
            method:="ordinary"
        end if;
        d := 0;
        while true do
            d1 := d;
            EG_delta(sys,vars,'M',`if`((method="random") and (d=0),"zero",method));
            n := LinearAlgebra:-RowDimension(M);
            M := M[1..n, 1..n];
            d := LinearAlgebra:-Determinant(M);
            s := sqrfree(d);
            d := `*`(op(map(z->z[1],s[2])));
            d := gcd(d, d1);
            if (degree(d1,x)=degree(d,x)) or (d=0) or (method<>"random") then break; end if;
        end do;
        d;
    end:

    ###################################################################
    # EG_delta - given a differential system, constructs an equivalent one (probably with
    #            some additional solutions), which has a non-singular leading matrix.
    # The input parameters are the system given as the list of its equations and the list of
    # the corresponding unknown functions. Optionally the third parameter may be also given
    # which is the name of variable to be assigned to the corresponding desingularized explicit
    # matrix. Optionally the forth parameter may be also given
    # which is the name of the method of a differential shift ("ordinary", "random", "zero" or "no"
    # "no" is not recommended as the infinite loop may happen if the system has dependent equations).
    ###################################################################

    EG_delta := proc(sys, vars)
        local M,n,m,ds,x,s,i,j,k,c,method;

        # Check the parameters
        n := nops(vars);
        x := select(type, indets(vars), name);
        if nops(x)=1 then
            x:=x[1];
        else
            error("Too many independent variables");
        end if;
        ds := indets(sys) minus {x};
        if nops(select(type, ds union indets(ds), name(identical(x))) minus {op(vars),x}) <> 0 then
            error("Unspecified unknown function in the given system");
        end if;

        # Construct the explicit matrix of the given system
        m := max(map(z->nops(indets(z))-2, select(has,indets(sys),diff)));
        M := Matrix(n,n*(m+1));
        s := copy(sys);
        for i to nops(sys) do
            for j to n do
                for k from m to 1 by -1 do
                    c:=coeff(s[i], diff(vars[j], x$k));
                    if c<>0 then
                        s[i] := dualnormal(s[i]-c*diff(vars[j],x$k));
                        M[i,(m-k)*n+j] := c
                    end if;
                end do;
            end do;
        end do;
        for i to nops(sys) do
            for j to n do
                M[i, m*n+j] := coeff(s[i], vars[j])
            end do;
        end do;

        # Determine the method to be used
        if nargs=3 and type(args[3],string) then
            method:=args[3]
        elif nargs=4 and type(args[3], name) and type(args[4],string) then
            method:=args[4]
        else
            method:="ordinary"
        end if;

        # Apply the EG_delta algorithm to the explicit matrix
        M := `EG_delta/doit`(M, m+1, x, method);

        # Construct the output
        # The desingularized explicit matrix if requested
        if nargs>=3 and type(args[3], name) then
            assign(args[3], copy(M[1]));
        end if;
        # The desingularized system
        s := [seq(add(add(M[1][i, (k-1)*n+j]*diff(vars[j],x$(m-k+1)), k=1..m) + M[1][i, m*n+j]*vars[j],j=1..n), i=1..nops(sys))];
        s;
    end: # EG_delta
    #######################################################################

    ###################################################################
    # `EG_delta/doit` - implements EG_delta algorithm applied to the given explicit matrix
    # The parameters are the explicit matrix, number of its blocks and the independent variable.
    # The implementation is based on the implementation of the EG' algorithm for LinearFunctionalSystem package.
    ###################################################################

    `EG_delta/doit` := proc(Mat, m, x, method)
        local
            k, l, n, WasShifted, IsZero, eg_elim, ExplicitMatrix, Row_Length,
            Shift_Row, DependentRows,
            rdim, cdim, err, ndx, z,
            fatum, len, nshifts;

        # some important parameters
        # Row and column dimensions
        if type(Mat, 'matrix') then
            rdim := linalg['rowdim'](Mat);
            cdim := linalg['coldim'](Mat);
        else
            rdim := LinearAlgebra:-RowDimension(Mat);
            cdim := LinearAlgebra:-ColumnDimension(Mat);
        end if;
        # The width of the block
        n := cdim/m;
        # It should be positive integer
        if not type(n, 'posint') then
            err := "Improper number of blocks";
            error(err);
        end if;

        # Width of a row
        Row_Length := proc(c)
            local
                k;
            option
                remember;
            for k from cdim by -1 to 1 do
                if ExplicitMatrix[c, k] <> 0 then
                    break;
                end if;
            end do;
            k;
        end:

        # The differential shift implementation
        if method="ordinary" then
            Shift_Row := proc(k,len)
                local dummy,den;
                forget(Row_Length);

                dummy := Vector[row](cdim,0);
                l := Row_Length(k);
                if l=0 then
                    return;
                end if;
                den := `if`(degree(ExplicitMatrix[k,l],x)=0, 1, ExplicitMatrix[k,l]);
                dummy[1..cdim-n] := LinearAlgebra:-Map(z->dualnormal(z/den), copy(ExplicitMatrix[k,n+1..cdim]));
                dummy := dummy + LinearAlgebra:-Map(z->dualnormal(diff(z,x)), dualnormal(ExplicitMatrix[k,1..cdim]/den));
                den := lcm(seq(denom(dummy[l]),l=1..cdim));
                dummy := LinearAlgebra:-Map(z->dualnormal(z*den), dummy);
                ExplicitMatrix[k,1..cdim] := eval(dummy);
            end:
        elif method="random" then
            fatum :=rand(0..1);
            Shift_Row := proc(k,len)
                local dummy,den;
                forget(Row_Length);

                dummy := Vector[row](cdim,0);
                l := Row_Length(k);
                if l=0 then
                    return;
                end if;
                if fatum()=1 then
                    den := `if`(degree(ExplicitMatrix[k,l],x)=0, 1, ExplicitMatrix[k,l]);
                    dummy[1..cdim-n] := LinearAlgebra:-Map(z->dualnormal(z/den), copy(ExplicitMatrix[k,n+1..cdim]));
                    dummy := dummy + LinearAlgebra:-Map(z->dualnormal(diff(z,x)), dualnormal(ExplicitMatrix[k,1..cdim]/den));
                    den := lcm(seq(denom(dummy[l]),l=1..cdim));
                    dummy := LinearAlgebra:-Map(z->dualnormal(z*den), dummy);
                else
                    dummy[1..cdim-n] := copy(ExplicitMatrix[k,n+1..cdim]);
                    dummy := dummy + LinearAlgebra:-Map(z->diff(z,x), ExplicitMatrix[k,1..cdim]);
                end if;
                ExplicitMatrix[k,1..cdim] := map(dualnormal,eval(dummy));
            end:
        elif method="zero" then
            Shift_Row := proc(k,len)
                local dummy,den,lz;
                forget(Row_Length);

                dummy := Vector[row](cdim,0);
                l := Row_Length(k);
                if l=0 then
                    return;
                end if;
                lz := n+1;
                while ExplicitMatrix[k,lz]=0 do lz:=lz+1 end do;
                if (lz<=2*n) and (l=len) then
                    den := `if`(degree(ExplicitMatrix[k,l],x)=0, 1, ExplicitMatrix[k,l]);
                    den := ExplicitMatrix[k,l];
                    dummy[1..cdim-n] := LinearAlgebra:-Map(z->dualnormal(z/den), copy(ExplicitMatrix[k,n+1..cdim]));
                    dummy := dummy + LinearAlgebra:-Map(z->dualnormal(diff(z,x)), dualnormal(ExplicitMatrix[k,1..cdim]/den));
                    den := lcm(seq(denom(dummy[l]),l=1..cdim));
                    dummy := LinearAlgebra:-Map(z->dualnormal(z*den), dummy);
                else
                    dummy[1..cdim-n] := copy(ExplicitMatrix[k,n+1..cdim]);
                    dummy := dummy + LinearAlgebra:-Map(z->diff(z,x), ExplicitMatrix[k,1..cdim]);
                end if;
                ExplicitMatrix[k,1..cdim] := map(dualnormal,eval(dummy));
            end:
        elif method="no" then
            Shift_Row := proc(k,len)
                local dummy,den,lz;
                forget(Row_Length);

                dummy := Vector[row](cdim,0);
                l := Row_Length(k);
                if l=0 then
                    return;
                end if;
                lz := n+1;
                while ExplicitMatrix[k,lz]=0 do lz:=lz+1 end do;
                dummy[1..cdim-n] := copy(ExplicitMatrix[k,n+1..cdim]);
                dummy := dummy + LinearAlgebra:-Map(z->diff(z,x), ExplicitMatrix[k,1..cdim]);
                ExplicitMatrix[k,1..cdim] := map(dualnormal,eval(dummy));
            end:
        end if;

        #######################################################################
        # Title: eg_elim
        #######################################################################
        eg_elim := proc()
            local
                MM, MM_T, ZM, v, e, noneliminated, len, c, i, j, k, l, r,
                d, ls, z, ci, d1, num, numi, rs, fatum, rh;

            forget(Row_Length);
            randomize;
            fatum := rand(2);

            MM := LinearAlgebra:-SubMatrix(ExplicitMatrix,1..rdim,1..n);
            len := sort([seq(k,k=1..rdim)],
                                    (i,j)->evalb(Row_Length(i)>Row_Length(j)));
            MM_T := LinearAlgebra:-Transpose(MM);

            v := map(dualnormal,LinearAlgebra:-NullSpace(MM_T));
            if v={} then
                [];
            else
                r := nops(v);
                ZM := LinearAlgebra:-Transpose(Matrix(rdim,r,[op(v)]));
                noneliminated := {seq(k,k=1..r)};
                ls := [];
                while nops(noneliminated)>0 do
                    num := 0;
                    l := 0;
                    for i in noneliminated do
                        numi := 0;
                        for j to rdim do
                            if ZM[i,len[j]]<>0 then
                                numi := j;
                                ci := len[j];
                                break;
                            end if;
                        end do;
                        if numi>num then
                            num := numi;
                            l := i;
                            c := ci;
                        else
                            if numi=num then
                                if nops(select(z->evalb(ZM[l,z]<>0),[seq(z,z=1..rdim)]))>
                                        nops(select(z->evalb(ZM[i,z]<>0),[seq(z,z=1..rdim)]))
                                then
                                    num := numi;
                                    l := i;
                                    c := ci;
                                else
                                    if fatum()=1 then
                                        num := numi;
                                        l := i;
                                        c := ci;
                                    end if;
                                end if;
                            end if;
                        end if;
                    end do;
                    if l=0 then
                        break;
                    end if;
                    noneliminated := noneliminated minus {l};
                    ls := [op(ls),[l,c]];
                    for k in noneliminated do
                        if k<>l then
                            if ZM[k,c]<>0 then
                                for i to rdim do
                                    if i<>c then
                                        ZM[k,i] := dualnormal(ZM[k,i]*ZM[l,c]-ZM[l,i]*ZM[k,c]);
                                    end if;
                                end do;
                                ZM[k,c] := 0;
                            end if;
                        end if;
                    end do;
                end do;
                for e in ls do
                    l := e[1];
                    d1 := lcm(op(map(z->denom(ZM[l,z]),[seq(z,z=1..rdim)])));
                    d := 0;
                    for i to rdim do
                        ZM[l,i] := dualnormal(d1*ZM[l,i]);
                        d := gcd(d,ZM[l,i]);
                    end do;
                    if has(d,x) then
                        for i to rdim do
                            ZM[l,i] := dualnormal(ZM[l,i]/d);
                        end do;
                    end if;
                    c := e[2];
                    ExplicitMatrix[c,1..cdim] := LinearAlgebra:-Map(dualnormal,
                                                    LinearAlgebra:-VectorMatrixMultiply(ZM[l,1..rdim],ExplicitMatrix));
                end do;
                ls;
            end if;
        end: #eg_elim
        #######################################################################

        #######################################################################
        # Start of `EG_delta/doit` main part

        # The explicit matrix to work with
        ExplicitMatrix := Matrix(rdim,cdim,Mat);

        #Initialization of some variables
        DependentRows := {};
        len := [seq(Row_Length(k),k=1..rdim)];

        # Main loop
        # it is to ensure the first invocation of eg_elim
        WasShifted := true;
        nshifts := 0;
        while true do
            # Check if there's zero rows in the marked matrix:
            ndx := {seq(z,z=1..rdim)} minus DependentRows;
            for k in ndx do
                IsZero := 1;
                while IsZero>0 do
                    for l from 1 to n do
                        if ExplicitMatrix[k,l]<>0 then
                            IsZero := 0;
                            break;
                        end if;
                    end do;
                    # if the k-th row is zero then we should shift it:
                    if IsZero>0 then
                        if IsZero<m then
                            IsZero := IsZero+1;
                            Shift_Row(k,len[k]);
                            nshifts := nshifts+1;
                            WasShifted := true;
                        else
                            IsZero := 0;
                            DependentRows := DependentRows union {k};
                        end if;
                    end if;
                end do;
            end do;
            # if there had been no shifts then we did it:
            if WasShifted then
                # step of eg-elimination:
                len := [seq(Row_Length(k),k=1..rdim)];
                eg_elim();
                WasShifted := false;
            else
                break;
            end if;
        end do;
        _SingSysShifts := nshifts;
        [ExplicitMatrix, DependentRows];
    end: # `EG_delta/doit`
    ###################################################################

    ###################################################################
    # EG_sigma - given a difference system, constructs an equivalent one (probably with
    #            some additional solutions), which has a non-singular leading or trailing matrix.
    # The input parameters are the system given as the list of its equations, the list of
    # the corresponding unknown functions and the direction ('lead' or 'trail').
    # Optionally the third parameter may be also given
    # which is the name of variable to be assigned to the corresponding desingularized explicit
    # matrix.
    ###################################################################

    EG_sigma := proc(sys, vars, lead_or_trail)
        local M,n,m,t,l,ds,x,s,i,j,k,c,method;

        # Check the parameters
        n := nops(vars);
        x := select(type, indets(vars), name);
        if nops(x)=1 then
            x:=x[1];
        else
            error("Too many independent variables");
        end if;
        ds := indets(sys) minus {x};
        if nops(select(type, ds union indets(ds), name(identical(x))) minus {op(vars),x}) <> 0 then
            error("Unspecified unknown function in the given system");
        end if;

        # Construct the explicit matrix of the given system
        t := max(map(z->op(z)-x, ds));
        l := min(map(z->op(z)-x, ds));
        m:=t-l;
        M := Matrix(n,n*(m+1));
        s := copy(sys);
        for i to nops(sys) do
            for j to n do
                for k from m to 0 by -1 do
                    c:=coeff(s[i], eval(vars[j], x=x+k+l));
                    if c<>0 then
                        M[i,(m-k)*n+j] := c
                    end if;
                end do;
            end do;
        end do;

        # Apply the EG_sigma algorithm to the explicit matrix
        M := `EG_sigma/doit`(M, m+1, x, lead_or_trail);

        # Construct the output
        # The desingularized explicit matrix if requested
        if nargs>=4 and type(args[4], name) then
            assign(args[4], [copy(M[1]),copy(M[2])]);
        end if;
        # The desingularized system
        s := [seq(add(add(factor(M[1][i, (k-1)*n+j])*eval(vars[j],x=x+(m-k+1)+l), k=1..m+1),j=1..n), i=1..nops(sys))];
        s;
    end; # EG_sigma
    ###################################################################

    ###################################################################
    # `EG_sigma/doit` - implements EG_sigma algorithm applied to the given explicit matrix
    # The parameters are the explicit matrix, number of its blocks, the independent variable
    # and the direction ('lead' or 'trail'). The optional fifth parameter (a boolean value)
    # may be given to indicate if a generic RHS transformation is needed to be computed.
    # The implementation is based on the implementation of the EG' algorithm for LinearFunctionalSystem package.
    ###################################################################

    `EG_sigma/doit` := proc(Mat, m, x, lead_or_trail)
        local
            k, l, n, WasShifted, IsZero, eg_elim, delta,
            Constraints, ExplicitMatrix, VertShifts, Row_Length,
            Shift_Row, Shift_Column, DependentRows,
            need_RHS, RHS, rdim, cdim, err, ndx, z;

        # some important parameters
        # If we need to compute a generic RHS transformations
        if nargs=5 then
            need_RHS := args[5];
        else
            need_RHS := false;
        end if;
        # Row and colum dimensions
        if type(Mat, 'matrix') then
            rdim := linalg['rowdim'](Mat);
            cdim := linalg['coldim'](Mat);
        else
            rdim := LinearAlgebra:-RowDimension(Mat);
            cdim := LinearAlgebra:-ColumnDimension(Mat);
        end if;
        # The width of the block
        n := cdim/m;
        # It should be positive integer
        if not type(n, 'posint') then
            err := "Improper number of blocks";
            error(err);
        end if;

        # some auxiliary variables and procedures depending on the lead_or_trail:
        delta := `if`(lead_or_trail = 'lead', 0, cdim-n);
        if lead_or_trail = 'lead' then
            Row_Length := proc(c)
                local
                    k;
                option
                    remember;
                for k from cdim by -1 to n+1 do
                    if ExplicitMatrix[c, k] <> 0 then
                        break;
                    end if;
                end do;
                trunc((k-1)/n);
            end:
            Shift_Row := proc(k);
                ExplicitMatrix[k,1..cdim-n]:=map(dualnormal,eval(ExplicitMatrix[k,n+1..cdim],x=x+1));
                ExplicitMatrix[k,cdim-n+1..cdim]:=0;
                if need_RHS then
                    RHS[k] := dualnormal(eval(`LinearFunctionalSystems/E`*RHS[k],x=x+1));
                end if;
            end:
        else
            Row_Length := proc(c)
                local
                    k;
                option
                    remember;
                for k from 1 to n*(m-1) do
                    if ExplicitMatrix[c, k] <> 0 then
                        break;
                    end if;
                end do;
                m-trunc((k-1)/n);
            end:
            Shift_Row := proc(k);
                ExplicitMatrix[k,n+1..cdim]:=map(dualnormal,eval(ExplicitMatrix[k,1..cdim-n],x=x-1));
                ExplicitMatrix[k,1..n]:=0;
                if need_RHS then
                    RHS[k] := dualnoemal(eval(`LinearFunctionalSystems/E`*RHS[k],x=x-1));
                end if;
            end:
        end if;

        #######################################################################
        # Title: eg_elim
        #######################################################################
        eg_elim := proc()
            local
                MM, MM_T, ZM, v, e, noneliminated, len, c, i, j, k, l, r,
                d, ls, z, ci, d1, num, numi, rs, fatum, rh;

            forget(Row_Length);
            randomize;
            fatum := rand(2);

            MM := LinearAlgebra:-SubMatrix(ExplicitMatrix,1..rdim,delta+1..delta+n);
            len := sort([seq(k,k=1..rdim)],
                            (i,j)->evalb(Row_Length(i)>Row_Length(j)));

            MM_T := LinearAlgebra:-Transpose(MM);

            v := map(simplify,LinearAlgebra:-NullSpace(MM_T),RootOf);
            if v={} then
                [];
            else
                r := nops(v);
                ZM := LinearAlgebra:-Transpose(Matrix(rdim,r,[op(v)]));
                noneliminated := {seq(k,k=1..r)};
                ls := [];
                while nops(noneliminated)>0 do
                    num := 0;
                    l := 0;
                    for i in noneliminated do
                        numi := 0;
                        for j to rdim do
                            if ZM[i,len[j]]<>0 then
                                numi := j;
                                ci := len[j];
                                break;
                            end if;
                        end do;
                        if numi>num then
                            num := numi;
                            l := i;
                            c := ci;
                        else
                            if numi=num then
                                if nops(select(z->evalb(ZM[l,z]<>0),[seq(z,z=1..rdim)]))>
                                        nops(select(z->evalb(ZM[i,z]<>0),[seq(z,z=1..rdim)]))
                                then
                                    num := numi;
                                    l := i;
                                    c := ci;
                                else
                                    if fatum()=1 then
                                        num := numi;
                                        l := i;
                                        c := ci;
                                    end if;
                                end if;
                            end if;
                        end if;
                    end do;
                    if l=0 then
                        break;
                    end if;
                    noneliminated := noneliminated minus {l};
                    ls := [op(ls),[l,c]];
                    for k in noneliminated do
                        if k<>l then
                            if ZM[k,c]<>0 then
                                for i to rdim do
                                    if i<>c then
                                        ZM[k,i] := dualnormal(ZM[k,i]*ZM[l,c]-ZM[l,i]*ZM[k,c]);
                                    end if;
                                end do;
                                ZM[k,c] := 0;
                            end if;
                        end if;
                    end do;
                end do;
                for e in ls do
                    l := e[1];
                    d1 := lcm(op(map(z->denom(ZM[l,z]),[seq(z,z=1..rdim)])));
                    d := 0;
                    for i to rdim do
                        ZM[l,i] := dualnormal(d1*ZM[l,i]);
                        d := gcd(d,ZM[l,i]);
                    end do;
                    if has(d,x) then
                        for i to rdim do
                            ZM[l,i] := dualnormal(ZM[l,i]/d);
                        end do;
                    end if;
                    c := e[2];
                    rs := roots(ZM[l,c],x);
                    if nops(rs)>0 then
                       rs := [seq(k[1], k=rs)];
                    end if;
                    rs := select(type, simplify(rs, 'symbolic'), integer);
                    if nops(rs) > 0 then
                        for r in rs do
                            if need_RHS then
                                v := [seq(dualnormal(eval(ExplicitMatrix[c,i],x=r)),i=1..m*n)];
                                rh := dualnormal(eval(RHS[c],x=r));
                                if nops(select(z->evalb(z<>0),v))>0 or (rh<>0) then
                                    v := [v, rh];
                                    if assigned(Constraints[r]) then
                                        Constraints[r] := [op(Constraints[r]),v];
                                    else
                                        Constraints[r] := [v];
                                    end if;
                                end if;
                            else
                                if assigned(Constraints[r]) then
                                    Constraints[r] := {op(Constraints[r]),[seq(dualnormal(eval(ExplicitMatrix[c,i],x=r)),i=1..cdim)]};
                                else
                                    Constraints[r] := {[seq(dualnormal(eval(ExplicitMatrix[c,i],x=r)),i=1..cdim)]};
                                end if;
                            end if;
                        end do;
                    end if;
                    ExplicitMatrix[c,1..cdim]:=LinearAlgebra:-Map(dualnormal,
                    LinearAlgebra:-VectorMatrixMultiply(ZM[l,1..rdim],ExplicitMatrix));
                    if need_RHS then
                        RHS[c] := dualnormal(add(ZM[l,k]*RHS[k],k=1..rdim));
                    end if;
                end do;
                ls
            end if;
        end: #eg_elim
        #######################################################################

        #######################################################################
        # Start of `EG_sigma/doit` main part

        # The explicit matrix to work with
        ExplicitMatrix := Matrix(rdim,cdim,Mat);
        #Initialization of some variables
        Constraints := table();
        DependentRows := {};
        if need_RHS then
            RHS := Vector(rdim,[seq(`LinearFunctionalSystems/s`[k],k=1..rdim)]);
        end if;
        # Main loop
        # it is to ensure the first invocation of eg_elim
        WasShifted := true;
        while true do
            # Check if there's zero rows in the marked matrix:
            ndx := {seq(z,z=1..rdim)} minus DependentRows;
            for k in ndx do
                IsZero := 1;
                while IsZero>0 do
                    for l from delta + 1 to delta + n do
                        if ExplicitMatrix[k,l]<>0 then
                            IsZero := 0;
                            break;
                        end if;
                    end do;
                    # if the k-th row is zero then we should shift it:
                    if IsZero>0 then
                        if IsZero<m then
                            IsZero := IsZero+1;
                            Shift_Row(k);
                            WasShifted := true;
                        else
                            IsZero := 0;
                            DependentRows := DependentRows union {k};
                        end if;
                    end if;
                end do;
            end do;
            # if there had been no shifts then we did it:
            if WasShifted then
                # step of eg-elimination:
                eg_elim();
                WasShifted := false;
            else
                break;
            end if;
        end do;
        if need_RHS then
            [ExplicitMatrix, eval(Constraints), RHS, DependentRows];
        else
            [ExplicitMatrix, eval(Constraints), DependentRows];
        end if;
    end: # `EG_sigma/doit`

    #######################################################################

    ###################################################################
    # EG_sigma - given a difference system, constructs an equivalent one (probably with
    #            some additional solutions), which has a non-singular leading or trailing matrix.
    # The input parameters are the system given as the list of its equations, the list of
    # the corresponding unknown functions and the direction ('lead' or 'trail').
    # Optionally the third parameter may be also given
    # which is the name of variable to be assigned to the corresponding desingularized explicit
    # matrix.
    ###################################################################

#    LaurentSolution := proc(Lfun, theta, var, deg0)
    LaurentSolution := proc(Lfun0)
        local M,n,n1,m,t,l,ds,s,i,j,k,c,method,z,EGSeq,ShiftsCount,deg, gamma,Constraints,e, r_min, r_max, nc, finished, p, rr, l0, sblk, nlin, ncol, cns, x, rec, sol, reci, m1, m2, m3, m4,
        ss, ndx, res, sol1,
        Lfun, theta, var, deg0;

userinfo(3, EG_sigma_infinite, `for solution`, M);
userinfo(3, EG_sigma_infinite, `for solution`, Constraints);


        if type(Lfun0, Matrix) then
            Lfun := eval(Lfun0);
            theta := args[2];
            var := args[3];
            deg0 := args[4];
            n := LinearAlgebra:-RowDimension(Lfun);
            if nargs=5 then
                gamma := Vector(n, args[5]);
            else
                gamma := Vector(n);
            end if;
        elif type(Lfun0, `+`) or type(Lfun0, `.`) then
            theta := args[2];
            var := op(args[3]);
            deg0 := args[4];
            Lfun := MatCoeffs(Lfun0,theta,args[3])[1];
            n := LinearAlgebra:-RowDimension(Lfun);
            if nargs=5 then
                gamma := Vector(n, args[5]);
            else
                gamma := Vector(n);
            end if;
        else
            error("The system to solve should be given either as a matrix or as a list of matrices");
        end if;



        #Compute the needed finite part
        l := 0;
        t := -m;        # Check the parameters

        EGSeq := [];
        Constraints := table();
        ShiftsCount := Vector(n);
        m := 1;
        while true do
            # Construct m-finite part of the explicit matrix of the given system
            M := Matrix(n,n*(m+1));
            for i from 0 to m do
                for j to n do
                    for k to n do
                        e := Lfun[k,j](i);
                        M[k,i*n+j]:=dualnormal(eval(e,theta=z-i));
                    end do;
               end do;
            end do;

            # Apply the EG_sigma algorithm to the explicit matrix
userinfo(3, EG_sigma_infinite, M);
            (M, EGSeq, ShiftsCount, gamma, finished) := op(`EG_sigma_infinite/doit`(M, m+1, z, EGSeq, ShiftsCount, gamma));
userinfo(3, EG_sigma_infinite, EGSeq);
            if finished then
                break
            end if;
            m:=m+1;
        end do;
        # Construct the output
userinfo(3, EG_sigma_infinite, `result`, M);
userinfo(3, EG_sigma_infinite, `result`, EGSeq);

n1:=n;n:='n';

n:=n1;
        p := dualnormal(LinearAlgebra:-LUDecomposition(M[1..n,1..n], 'output'='determinant'));

        rr := roots(p,z);
        if nops(rr)>0 then
          rr := [seq(k[1], k=rr)];
        end if;
        rr := simplify(rr,'symbolic');
        rr := select(type, rr, integer);
        if nops(rr)>0 then
            rr := sort(rr);
        else
            return(NULL);
        end if;

        r_min := rr[1];
        r_max := rr[-1];

        nc := map(a->op(map(b->op(b[3]),a[2])),EGSeq);
        nc := select(b->evalb(b>=r_min),nc);
        if nops(nc)>0 then
            nc := sort(nc)[-1];
        else
            nc := -infinity;
        end if;

        l0 := max(r_max,nc);
        deg := max(deg0,l0);
        m:=deg-r_min+max(ShiftsCount);

        # Construct m-finite part of the explicit matrix of the given system
        M := Matrix(n,n*(m+1));
        for i from 0 to m do
            for j to n do
                for k to n do
                    e := Lfun[k,j](i);
                    M[k,i*n+j]:=dualnormal(eval(e,theta=z-i));
                end do;
            end do;
        end do;

        (M, Constraints) := ApplyEGseq(M, EGSeq, z, true);

        sblk :=n; nlin :=n; ncol :=m+1;
        cns := Constraints; x := z;

        rec := M;

        sol := table();
        for i from r_min to deg do
          reci := eval(rec,x=i);
          for k to nlin do
            c := 0;
            for m1 from 1 to ncol do
                if (i-m1+1>=r_min) then
                    for m2 to sblk do
                        c := c+reci[k,(m1-1)*sblk+m2]*sol[m2,i-m1+1];
                    end do;
                end if;
            end do;
            c := dualnormal(c);
            ss := select(type,indets(c),`sol`[anything,anything]);

            if nops(ss)>0 then
                ndx := 1;
                for m3 from 2 to nops(ss) do
                    if op(2,ss[ndx])<op(2,ss[m3]) then
                        ndx := m3;
                    elif (op(2,ss[ndx])=op(2,ss[m3])) and (op(1,ss[ndx])<op(1,ss[m3])) then
                        ndx := m3;
                    end if;
                end do;

                c := collect(c, ss[ndx]);
                sol[op(1,ss[ndx]),op(2,ss[ndx])] :=
                    dualnormal(-eval(c,ss[ndx]=0)/coeff(c,ss[ndx]));
                sol := map(dualnormal,map(eval,sol));
            elif c<>0 then
                return(NULL);
            end if;
          end do;
        end do;
        # Form the solution
        sol1 := map(dualnormal,map(eval, copy(sol), 'sol'='sol1'));
        ndx := 0;
        for i to sblk do
          for k from r_min to deg do
            if not assigned(sol1[i,k]) then
              ndx := ndx + 1;
              sol1[i,k] := _c[ndx];
            end if;
          end do;
        end do;
        s := Array(1..sblk);
        for i to sblk do
          s[i] := add(var^(k)*eval(sol1[i,k]),k=r_min..deg);
        end do;
        s := convert(s,'list');
        # Take into consideration additional constraints:
        for i in map(op,[indices(cns)]) do
            if i>=r_min then
                for m3 to nops(cns[i]) do
                    reci := cns[i][m3];
                    c := 0;
                    for m1 from 1 to ncol do
                        if (i-m1+1>=r_min) then
                            for m2 to sblk do
                                c := c+reci[(m1-1)*sblk+m2]*sol[m2,i-m1+1];
                            end do;
                        end if;
                    end do;
                    c := dualnormal(c);
                    ss := select(type,indets(c),`sol`[anything,anything]);
                    if nops(ss)>0 then
                        ndx := 1;
                        for m4 from 2 to nops(ss) do
                            if op(2,ss[ndx])<op(2,ss[m4]) then
                                ndx := m4;
                            elif (op(2,ss[ndx])=op(2,ss[m4])) and (op(1,ss[ndx])<op(1,ss[m4])) then
                                ndx := m4;
                            end if;
                        end do;

                        c := collect(c, ss[ndx]);
                        sol[op(1,ss[ndx]),op(2,ss[ndx])] :=
                            dualnormal(-eval(c, ss[ndx]=0)/coeff(c,ss[ndx]));
                        sol := map(dualnormal,map(eval,sol));
                    elif c<>0 then
                        return(NULL);
                    end if;
                end do;
            end if;
        end do;
        # Form the solution
        ndx := 0;
        for i to sblk do
          for k from r_min to deg do
            if not assigned(sol[i,k]) then
              ndx := ndx + 1;
              sol[i,k] := _c[ndx];
            end if;
          end do;
        end do;
        sol := map(dualnormal,map(eval,sol));

        s := Array(1..sblk);
        for i to sblk do
          s[i] := add(var^(k)*eval(sol[i,k]),k=r_min..deg);
        end do;
        if s<>NULL then
          s := convert(s,'list');
          res := table();
          res['initial'] := s;
          res['degree'] := m;
          res['recurrence'] := [eval(rec),[],Vector(nlin)];
          res['coefficients'] := sol;
          res['the_case'] := case;
          res['lead'] := l;
          res['trail'] := t;
          res['variable'] := var;
          res['index'] := ndx;
          res['q_par'] := q;
          res['homogeneous'] := true;
          s,res;
        else
          NULL;
        end if;
        setattribute([seq(s[i]+O(var^(deg+1)),i=1..nops(s))], res);

    end; # EG_sigma_infinite

    ###################################################################

    #######################################################################
    ApplyEGseq:=proc(ExplicitMatrix, EG_seq, x, need_constraints)
        local cdim, rdim, n, Constraints, i, k, s, r, need_RHS, RHS, v, rh;
           cdim := LinearAlgebra:-ColumnDimension(ExplicitMatrix);
           rdim := LinearAlgebra:-RowDimension(ExplicitMatrix);
           n := LinearAlgebra:-RowDimension(ExplicitMatrix);
           if need_constraints then
              Constraints := table();
           end if;
           if nargs=5 then
              need_RHS := args[5];
           else
              need_RHS := false;
           end if;
           if need_RHS then
              RHS := Vector(rdim,[seq(`EG/s`[i],i=1..rdim)]);
           end if;
           for s in EG_seq do
              for k in s[1] do
                  ExplicitMatrix[k,1..cdim-n]:=map(dualnormal,eval(ExplicitMatrix[k,n+1..cdim],x=x+1));
                  ExplicitMatrix[k,cdim-n+1..cdim]:=0;
                  if need_RHS then
                     RHS[k] := dualnormal(eval(`EG/E`*RHS[k],x=x+1));
                  end if;
              end do;
              for k in s[2] do
                  if need_constraints then
                     if nops(k[3]) > 0 then
                        for r in k[3] do
                           if need_RHS then
                              v := [seq(dualnormal(eval(ExplicitMatrix[k[1],i],x=r)),i=1..cdim)];
                              rh := dualnormal(eval(RHS[k[1]],x=r));
                              if nops(select(z->evalb(z<>0),v))>0 or (rh<>0) then
                                 v := [v, rh];
                                 if assigned(Constraints[r]) then
                                    Constraints[r] := [op(Constraints[r]),v];
                                 else
                                    Constraints[r] := [v];
                                 end if;
                              end if;
                            else
                                if assigned(Constraints[r]) then
                                   Constraints[r] := {op(Constraints[r]),[seq(dualnormal(eval(ExplicitMatrix[k[1],i],x=r)),i=1..cdim)]};
                                else
                                   Constraints[r] := {[seq(dualnormal(eval(ExplicitMatrix[k[1],i],x=r)),i=1..cdim)]};
                                end if;
                            end if;
                        end do;
                    end if;
                  end if;
                  ExplicitMatrix[k[1],1..cdim]:=LinearAlgebra:-Map(dualnormal,
                       LinearAlgebra:-VectorMatrixMultiply(k[2],ExplicitMatrix));
                  if need_RHS then
                    RHS[k[1]] := dualnormal(add(k[2][i]*RHS[i],i=1..rdim));
                  end if;
             end do;
           end do;
           if need_constraints then
              if need_RHS then
                 copy(ExplicitMatrix), copy(Constraints), copy(RHS);
              else
                 copy(ExplicitMatrix), copy(Constraints);
              end if;
           else
              if need_RHS then
                 copy(ExplicitMatrix), copy(RHS);
              else
                 copy(ExplicitMatrix);
              end if;
           end if;
    end:

    #######################################################################

    ###################################################################
    # `EG_sigma_infinite/doit` - implements EG_sigma_infinite algorithm applied to the given explicit matrix
    # The parameters are the explicit matrix, number of its blocks, the independent variable
    # and the direction ('lead' or 'trail'). The optional fifth parameter (a boolean value)
    # may be given to indicate if a generic RHS transformation is needed to be computed.
    # The implementation is based on the implementation of the EG' algorithm for LinearFunctionalSystem package.
    ###################################################################

    `EG_sigma_infinite/doit` := proc(Mat, m, x, EG_seq_0, ShiftsCount0,gamma0)
        local
            k, l, WasShifted, IsZero, eg_elim, delta,
            ExplicitMatrix, VertShifts, Row_Length,
            Shift_Row, Shift_Column, DependentRows,
            rdim, cdim, err, ndx, z,
            n, gamma, EG_seq, ShiftsCount, shifts, finished, elims;

        # some important parameters
        # Row and colum dimensions
        rdim := LinearAlgebra:-RowDimension(Mat);
        cdim := LinearAlgebra:-ColumnDimension(Mat);
        # The width of the block
        n := cdim/m;

        # some auxiliary variables and procedures depending on the lead_or_trail:
        gamma := eval(gamma0);
        Row_Length := proc(c)
           local
              k;
           option
              remember;
           gamma[c];
        end:
        Shift_Row := proc(k);
           ExplicitMatrix[k,1..cdim-n]:=map(dualnormal,eval(ExplicitMatrix[k,n+1..cdim],x=x+1));
           ExplicitMatrix[k,cdim-n+1..cdim]:=0;
        end:

        #######################################################################
        # Title: eg_elim
        #######################################################################
        eg_elim := proc()
            local
                MM, MM_T, ZM, v, e, noneliminated, len, c, i, j, k, l, r,
                d, ls, z, ci, d1, num, numi, rs, fatum, rh, res;

            forget(Row_Length);
            randomize;
            fatum := rand(2);

            MM := LinearAlgebra:-SubMatrix(ExplicitMatrix,1..rdim,1..n);

            MM_T := LinearAlgebra:-Transpose(MM);

            v := map(dualnormal,LinearAlgebra:-NullSpace(MM_T));
            if v={} then
                [];
            else
                r := nops(v);
                ZM := LinearAlgebra:-Transpose(Matrix(rdim,r,[op(v)]));
                for l to r do
                    d1 := lcm(op(map(z->denom(ZM[l,z]),[seq(z,z=1..rdim)])));
                    d := 0;
                    for i to rdim do
                        ZM[l,i] := dualnormal(d1*ZM[l,i]);
                        d := gcd(d,ZM[l,i]);
                    end do;
                end do;
                noneliminated := {seq(k,k=1..r)};
                ls := [];
                while nops(noneliminated)>0 do
                    num := 0;
                    l := 0;
                    for i in noneliminated do
                        len := sort([seq(k,k=1..rdim)],
                            (i1,j1)->evalb(Row_Length(i1)+degree(ZM[i,i1],x)>Row_Length(j1)+degree(ZM[i,j1],x)));
                        numi := 0;
                        for j to rdim do
                            if ZM[i,len[j]]<>0 then
                                numi := j;
                                ci := len[j];
                                break;
                            end if;
                        end do;
                        if numi>num then
                            num := numi;
                            l := i;
                            c := ci;
                        else
                            if numi=num then
                                if nops(select(z->evalb(ZM[l,z]<>0),[seq(z,z=1..rdim)]))>
                                        nops(select(z->evalb(ZM[i,z]<>0),[seq(z,z=1..rdim)]))
                                then
                                    num := numi;
                                    l := i;
                                    c := ci;
                                else
                                    if fatum()=1 then
                                        num := numi;
                                        l := i;
                                        c := ci;
                                    end if;
                                end if;
                            end if;
                        end if;
                    end do;
                    if l=0 then
                        break;
                    end if;
                    noneliminated := noneliminated minus {l};
                    ls := [op(ls),[l,c]];
                    for k in noneliminated do
                        if k<>l then
                            if ZM[k,c]<>0 then
                                for i to rdim do
                                    if i<>c then
                                        ZM[k,i] := dualnormal(ZM[k,i]*ZM[l,c]-ZM[l,i]*ZM[k,c]);
                                    end if;
                                end do;
                                ZM[k,c] := 0;
                            end if;
                        end if;
                    end do;
                end do;
                elims :=[];
                for e in ls do
                    l := e[1];
                    if has(d,x) then
                        for i to rdim do
                            ZM[l,i] := dualnormal(ZM[l,i]/d);
                        end do;
                    end if;
                    c := e[2];
                    rs := roots(ZM[l,c],x);
                    if nops(rs)>0 then
                       rs := [seq(k[1], k=rs)];
                    end if;
                    rs := select(type, simplify(rs, 'symbolic'), integer);
                    ExplicitMatrix[c,1..cdim]:=LinearAlgebra:-Map(dualnormal,
                        LinearAlgebra:-VectorMatrixMultiply(ZM[l,1..rdim],ExplicitMatrix));
                    res := ShiftsCount[c];
                    for k from 1 to rdim do
                        if ZM[l,k]<>0 then
                            res := max(res, ShiftsCount[k]);
                        end if;
                    end do;
                    ShiftsCount[c] := res;
                    gamma[c] := gamma[c]+ degree(ZM[l,c]);
                    elims := [op(elims),[c,eval(ZM[l,1..rdim]),rs]];
                end do;
                elims;
            end if;
        end; #eg_elim
        #######################################################################

        #######################################################################
        # Start of `EG_sigma_infinite/doit` main part

        # The explicit matrix to work with
        ExplicitMatrix := Matrix(rdim,cdim,Mat);
        ExplicitMatrix := ApplyEGseq(ExplicitMatrix, EG_seq_0, x, false);
userinfo(5, EG_sigma_infinite, ExplicitMatrix);
        EG_seq:=[op(EG_seq_0)];
        #Initialization of some variables
        ShiftsCount := eval(ShiftsCount0);
        # Main loop
        # it is to ensure the first invocation of eg_elim
        WasShifted := true;
        while true do
            # Check if there's zero rows in the marked matrix:
            ndx := {seq(z,z=1..rdim)};
            shifts:=[];
            for k in ndx do
                finished := false;
                IsZero[k] := 0;
                while not finished do
                    for l from 1 to n do
                        if ExplicitMatrix[k,l]<>0 then
                            finished := true;
                            break;
                        end if;
                    end do;
                    # if the k-th row is zero then we should shift it:
                    if not finished then
                        if ShiftsCount[k]+IsZero[k]<m-1 then
                            Shift_Row(k);
userinfo(7, EG_sigma_infinite, ExplicitMatrix[1..n,1..n]);
                            shifts:=[op(shifts),k];
                            WasShifted := true;
                            IsZero[k] := IsZero[k]+1;
                        else
                            finished := false;
                            break;
                        end if;
                    end if;
                end do;
                if not finished then
                   break;
                end if;
            end do;
userinfo(7, EG_sigma_infinite, ShiftsCount);
            # if there had been no shifts then we did it:
            if WasShifted and finished then
                for k in ndx do
                    ShiftsCount[k] := ShiftsCount[k]+IsZero[k];
                end do;
                # step of eg-elimination:
userinfo(5, EG_sigma_infinite, ExplicitMatrix);
                elims := eg_elim();
userinfo(5, EG_sigma_infinite, ExplicitMatrix);
userinfo(7, EG_sigma_infinite, ShiftsCount);
                EG_seq := [op(EG_seq),[eval(shifts),eval(elims)]];
userinfo(7, EG_sigma_infinite, ExplicitMatrix[1..n,1..n]);
                WasShifted := false;
            else
                break;
            end if;
        end do;

        [ExplicitMatrix, EG_seq, eval(ShiftsCount), eval(gamma), finished];
    end; # `EG_sigma_infinite/doit`
#######################################################################


    ###################################################################
    # EG_sigma - given a difference system, constructs an equivalent one (probably with
    #            some additional solutions), which has a non-singular leading or trailing matrix.
    # The input parameters are the system given as the list of its equations, the list of
    # the corresponding unknown functions and the direction ('lead' or 'trail').
    # Optionally the third parameter may be also given
    # which is the name of variable to be assigned to the corresponding desingularized explicit
    # matrix.
    ###################################################################

    RegularSolutionComponent := proc(Lfun, EGSeq, z, alpha, cursol0, mm, theta, s, var, ldeg, deg, m)
        local M,n,n1,t,l,ds,i,i1,j,j1,k,c,e, r_min, r_max, nc, finished, p, rr, l0, sblk, nlin, ncol, cns, x, rec, sol, reci, m1, m2, m3, m4, rh, ss0,
        ss, ndx, res, sol1,rhside,cursol;

        n:=LinearAlgebra:-RowDimension(Lfun);
        # Construct m-finite part of the explicit matrix of the given system
        M := Matrix(n,n*(m+1));
        for i from 0 to m do
            for j to n do
                for k to n do
                    e := Lfun[k,j](i);
                    M[k,i*n+j]:=dualnormal(eval(e,theta=z-i));
                end do;
            end do;
        end do;

        M := map(dualnormal,eval(M,z=z+alpha));
#        (M, cns, rh) := ApplyEGseq(M,  EGSeq, z, true, true);
        (M, cns, rh) := ApplyEGseq(M,  map(dualnormal,eval(EGSeq,z=z+alpha)),z, true, true);

        cursol := copy(cursol0);
        for k to mm-1 do
           cursol := RegularSolutionComponent(Lfun, EGSeq, z, alpha, cursol, k, theta, s, var, ldeg, deg+s*(mm-k), m+s*(mm-k));
        end do;

        #compute RHS of the system to be solved
        rhside := ComputeRHS(cursol, mm, rh, var, Lfun, theta, deg+s);
        sblk :=n; nlin :=n; ncol :=m+1;

        r_min := min(0, ldeg, min(op(map(ldegree,rhside,var))));

        rec := copy(M);
        sol := table();
        for i from r_min to deg do
          reci := map(dualnormal,eval(rec, z=i));
          for k to nlin do
            c := 0;
            for m1 from 1 to ncol do
                if (i-m1+1>=r_min) then
                    for m2 to sblk do
                        c := c+reci[k,(m1-1)*sblk+m2]*sol[m2,i-m1+1];
                    end do;
                end if;
            end do;
            c := dualnormal(c-eval(coeff(rhside[k],var,i),z=i));
           ss0 := indets(c) minus {n};
           ss := select(type,ss0,`sol`[anything,anything]);

            if nops(ss)>0 then
                ndx := 1;
                for m3 from 2 to nops(ss) do
                    if op(2,ss[ndx])<op(2,ss[m3]) then
                        ndx := m3;
                    elif (op(2,ss[ndx])=op(2,ss[m3])) and (op(1,ss[ndx])<op(1,ss[m3])) then
                        ndx := m3;
                    end if;
                end do;

                c := collect(c, ss[ndx]);
                sol[op(1,ss[ndx]),op(2,ss[ndx])] :=
                    dualnormal(-eval(c,ss[ndx]=0)/coeff(c,ss[ndx]));
                sol := map(dualnormal,map(eval,sol));
                cursol := map(dualnormal,map2(subs,ss[ndx]=-eval(c,ss[ndx]=0)/coeff(c,ss[ndx]),cursol));
                rhside := map(dualnormal,map2(subs,ss[ndx]=-eval(c,ss[ndx]=0)/coeff(c,ss[ndx]),rhside));
            elif (c<>0) and nops(ss0)=0 then
              return(NULL);
            elif c<>0 then
              c := collect(c, ss0[1]);
              sol := map(dualnormal,map2(subs,ss0[1]=-eval(c,ss0[1]=0)/coeff(c,ss0[1]),sol));
              cursol := map(dualnormal,map2(subs,ss0[1]=-eval(c,ss0[1]=0)/coeff(c,ss0[1]),cursol));
              rhside := map(dualnormal,map2(subs,ss0[1]=-eval(c,ss0[1]=0)/coeff(c,ss0[1]),rhside));

              if nops(select(z->evalb(z<>0),cursol[1][1]))=0 then
                return(NULL);
              end if;
            end if;

          end do;
        end do;
        # Form the solution
        sol1 := map(eval, copy(sol), 'sol'='sol1');
        ndx := 0;
        for i to sblk do
          for k from r_min to deg do
            if not assigned(sol1[i,k]) then
              ndx := ndx + 1;
              sol1[i,k] := _c[mm,ndx];
            end if;
          end do;
        end do;
        ss := Array(1..sblk);
        for i to sblk do
          ss[i] := add(var^(k)*eval(sol1[i,k]),k=r_min..deg);
        end do;
        ss := convert(ss,'list');
        # Take into consideration additional constraints:
        for i in map(op,[indices(cns)]) do
            if i>=r_min then
                for m3 to nops(cns[i]) do
                    reci := cns[i][m3][1];
                    c := 0;
                    for m1 from 1 to ncol do
                        if (i-m1+1>=r_min) then
                            for m2 to sblk do
                                c := c+reci[(m1-1)*sblk+m2]*sol[m2,i-m1+1];
                            end do;
                        end if;
                    end do;
                    rhside := ComputeRHS(cursol, mm, [cns[i][m3][2]], var, Lfun, theta, deg);
                    rhside := dualnormal(eval(rhside, z = z + alpha));
                    c := dualnormal(c-eval(coeff(rhside[1],var,i),z=i));
                    ss0 := indets(c) minus {n};
                    ss := select(type,ss0,`sol`[anything,anything]);

                    if nops(ss)>0 then
                        ndx := 1;
                        for m4 from 2 to nops(ss) do
                            if op(2,ss[ndx])<op(2,ss[m4]) then
                                ndx := m4;
                            elif (op(2,ss[ndx])=op(2,ss[m4])) and (op(1,ss[ndx])<op(1,ss[m4])) then
                                ndx := m4;
                            end if;
                        end do;
                        c := collect(c, ss[ndx]);
                        sol[op(1,ss[ndx]),op(2,ss[ndx])] :=
                            dualnormal(-eval(c, ss[ndx]=0)/coeff(c,ss[ndx]));
                        cursol := map(dualnormal,map2(subs,ss[ndx]=-eval(c,ss[ndx]=0)/coeff(c,ss[ndx]),cursol));
                        sol := map(dualnormal,map(eval,sol));
                    elif (c<>0) and nops(ss0)=0 then
                      return(NULL);
                    elif c<>0 then
                      c := collect(c, ss0[1]);
                      sol := map(dualnormal,map2(subs,ss0[1]=-eval(c,ss0[1]=0)/coeff(c,ss0[1]),sol));
                      cursol := map(dualnormal,map2(subs,ss0[1]=-eval(c,ss0[1]=0)/coeff(c,ss0[1]),cursol));

                      if nops(select(z->evalb(z<>0),cursol[1][1]))=0 then
                        return(NULL);
                    end if;
                  end if;
                end do;
            end if;
        end do;
        # Form the solution
        ndx := 0;
        for i to nlin do
          for k from r_min to deg do
             if not assigned(sol[i,k]) then
                ndx := ndx + 1;
                sol[i,k] := _c[mm,ndx];
             end if;
          end do;
        end do;
        sol := map(eval,sol);
        ss := Array(1..sblk);
        for i to sblk do
          ss[i] := add(var^(k)*eval(sol[i,k]),k=r_min..deg);
        end do;
        ss := convert(ss,'list');

        if nops(select(z->evalb(z<>0),ss))=0 then
          return(NULL);
        end if;

        sol1 := table();
        for i1 to nlin do
           for j1 from deg+2-ncol to deg do
             if assigned(sol[i1,j1]) then
               sol1[i1,j1] := sol[i1,j1];
             else
               sol1[i1,j1] := 0;
             end if;
           end do;
         end do;
         sol := eval(sol1);
         if mm>nops(cursol) then
           [op(cursol),[ss,eval(sol),deg]];
         else
           cursol[mm]:=[ss,eval(sol),deg];
           cursol;
         end if;
    end; # RegularSolutionComponent
#######################################################################


#######################################################################
# Module: LinearFunctionalSystems
# Submodule: RegSol
# Name  : ComputeRHS (local member)
#
# Input:
#     sol0 - previous solutions involved in computing the recurrence's RHS
#     rh - the recurrence's RHS in the generic form
#     x - expression to which `LinearFunctionalSystems/E` corresponds in the generic RHS
#     funs - indeterminate functions
#     L - operators
#
# Output:
#     the recurrence's RHS
#
#######################################################################

    ComputeRHS := proc(sol0, m, rh, x, Lfun, theta, l)
      local i, j, n, sol, k, d, c, s, e, q, sbs, res;

      sol := sol0;
      # Number of indeterminate functions
      n := LinearAlgebra:-RowDimension(Lfun);

      res := [seq(0,k=1..n)];

      # Compute rhs of the original system
      for i from 1 to m-1 do
        s:=table();
        s[0] := copy(sol[m-i][1]);
        for q from 0 to l do
          for k from 1 to n do
            for j from 1 to n do
              e := collect(Lfun[k,j](q), theta);
              for d from 1 to degree(e, theta) do
                  if d>=i then
                     c := coeff(e, theta, d)*x^q;
                     if not assigned(s[d-i]) then
                        s[d-i] := copy(map(z->dualnormal(x*diff(z,x),expanded),s[d-i-1]));
                     end if;
                     res[k] := dualnormal(res[k] + c*binomial(d,i)*s[d-i][j]);
                  end if;
              end do;
            end do;
          end do;
        end do;
      end do;
      res := -res;

      #Compute rhs of the induced recurrence
      sbs := [seq(`EG/s`[k]=res[k],k=1..n),`EG/E`=x^(-1)];
      map(dualnormal,convert(subs(sbs,rh),list));
    end;
#######################################################################





#######################################################################
# Module: LinearFunctionalSystems
# Submodule: RegSol
# Name  : RegularSolution
#         (exported member to both LinearFunctionalSystems and RegSol)
#
# Input:
#     sys - system (list) of differential
#       equations
#     vars - list of function to solve for
#     x - variable
#
# Output:
#     the regular solution of linear differential system of equations
#
#######################################################################

#RegularSolution := proc(Lfun, theta, var, deg0)
RegularSolution := proc(Lfun0)
    local
      rM, pp, newargs, homo, sol, v, k, res, x, sys0, funs,
      GetLm, L, Lm, Ls, M, MM, Ms, RootsClassesRepresentatives, Y, Yd,
      alpha, cns, deg, f, ldeg, m, ncol, nlin, p, rReps,
      rr, size, sol_alpha, solm, sys, sblk, r, z, opts, ARGS, pnt, dummy, params,
      n, EGSeq, Constraints,ShiftsCount,i,j,e,gamma,finished,n1,EGSeqM,r_max,r_min,nc,l,l1,s,
      Lfun, theta, var, deg0;
    option
      `Copyright (c) 1999 Waterloo Maple Inc. All rights reserved.`;


    RootsClassesRepresentatives := proc(a,x)
      local res, K, n, newone, pf, pfs, qf;
      res := [];
      if has(a, RootOf) then
        # Case of algebraic numbers
        p := collect(simplify(a, 'RootOf'), x);
        # Field extension:
        K := indets(p, RootOf);
        pfs := map2(op,1,factors(p, K)[2]);
      else
        # Case of rational numbers
        p := collect(a, x);
        pfs := map2(op,1,factors(p)[2]);
      end if;
      # Try all possible pairs of factors:
      for pf in pfs do
        newone := true;
        for qf in res do
          n := degree(pf, x);
          # First test - degrees should be equal:
          if n <> degree(qf, x) then
            next;
          end if;
          # Possible shift:
          alpha := (coeff(qf, x, n - 1) - coeff(pf, x , n - 1))/n;
          # Second test - possible shift should be integer:
          if not type(alpha, integer) then
            next;
          end if;
          # Last test - substitution:
          if (n > 1) and
            (collect(subs(x = x + alpha, pf) - qf, x, dualnormal) <> 0 ) then
            next;
          end if;
          newone := false;
          break;
        end do;
        if newone then
          res := [op(res), pf];
        end if;
      end do;

      res := select(has,res,x);

      res := map(RootOf,res,x);
      res := map(z->`if`(type(z,integer),0,
                   `if`(type(z,rational),z-floor(z),
                        `if`(has(z,RootOf),z-eval(z,RootOf=0)+`if`(type(eval(z,RootOf=0),integer), 0, eval(z,RootOf=0)-floor(eval(z,RootOf=0))),
                           z
                         )
                       )
                     ),
                 res);
      res
    end;

        # Check the parameters
        if type(Lfun0, Matrix) then
            Lfun := eval(Lfun0);
            theta := args[2];
            var := args[3];
            deg0 := args[4];
            n := LinearAlgebra:-RowDimension(Lfun);
            if nargs=5 then
                gamma := Vector(n, args[5]);
            else
                gamma := Vector(n);
            end if;
        elif type(Lfun0, `+`) or type(Lfun0, `.`) then
            theta := args[2];
            var := op(args[3]);
            deg0 := args[4];
            Lfun := MatCoeffs(Lfun0,theta,args[3])[1];
            n := LinearAlgebra:-RowDimension(Lfun);
            if nargs=5 then
                gamma := Vector(n, args[5]);
            else
                gamma := Vector(n);
            end if;
        else
            error("The system to solve should be given either as a matrix or as a list of matrices");
        end if;


        EGSeq := [];
        Constraints := table();
        ShiftsCount := Vector(n);
        m := 1;
        while true do
            # Construct m-finite part of the explicit matrix of the given system
            M := Matrix(n,n*(m+1));
            for i from 0 to m do
                for j to n do
                    for k to n do
                        e := Lfun[k,j](i);
                        M[k,i*n+j]:=dualnormal(eval(e,theta=z-i));
                    end do;
               end do;
            end do;
            # Apply the EG_sigma algorithm to the explicit matrix
userinfo(3, EG_sigma_infinite, M);
            (M, EGSeq, ShiftsCount, gamma, finished) := op(`EG_sigma_infinite/doit`(M, m+1, z, EGSeq, ShiftsCount, gamma));
userinfo(3, EG_sigma_infinite, EGSeq);
            if finished then
                break
            end if;
            m:=m+1;
        end do;
        # Construct the output
userinfo(3, EG_sigma_infinite, `result`, M);
userinfo(3, EG_sigma_infinite, `result`, EGSeq);

n1:=n;n:='n';
n:=n1;
        p := dualnormal(LinearAlgebra:-LUDecomposition(M[1..n,1..n], 'output'='determinant'));

    rReps := sort(RootsClassesRepresentatives(p,z));
    if nops(rReps)=0 then
       return(NULL);
    end if;
    sol := [];
    Ls := [];
    Ms := [];
    for alpha in rReps do
      MM := map(dualnormal,eval(M,z=z+alpha));
      EGSeqM :=  map(dualnormal,eval(EGSeq,z=z+alpha));
      p := dualnormal(LinearAlgebra:-LUDecomposition(MM[1..n,1..n], 'output'='determinant'));
      rr := roots(p,z);
      if nops(rr)>0 then
        rr := [seq(k[1], k=rr)];
      end if;
      rr := select(type, simplify(rr, 'symbolic'), integer);

      if nops(rr)>0 then
        rr := sort(rr);
        r_max[alpha] := rr[-1];
        r_min[alpha] := rr[1];
      else
        r_max[alpha] := -infinity;
        r_min[alpha] := infinity;
      end if;

      nc[alpha] := select(type,map(a->op(map(b->op(b[3]),a[2])),EGSeqM),integer);
      nc[alpha] := select(b->evalb(b>=r_min[alpha]),nc[alpha]);
      if nops(nc[alpha])>0 then
        nc[alpha] := sort(nc[alpha])[-1];
      else
        nc[alpha] := -infinity;
      end if;
    end do;

    l := max(seq(max(r_max[alpha],nc[alpha]),alpha=rReps));
    l := max(l,deg0);
    s := max(ShiftsCount);
    l1 := max(seq(l-r_min[alpha]+s,alpha=rReps));
    for alpha in rReps do
      sol_alpha := [];
      m := 0;
      while true do
        solm := RegularSolutionComponent(Lfun, EGSeq, z, alpha, sol_alpha, m+1, theta, s, var, r_min[alpha], l, l1);
        if solm=NULL then
          break;
        else
          sol_alpha := solm;
          m := m+1;
        end if;
      end do;
      if sol_alpha<>[] then
        sol := [op(sol),[alpha, sol_alpha]];
      end if;
    end do;

    if sol=[] then
      sol := [seq(0, k=1..sblk)];
    else
      sol := Combine(sol,var,true);
    end if;
    sol;
end;
#######################################################################

#######################################################################
# Module: LinearFunctionalSystems
# Submodule: RegSol
# Name  : Combine (local member)
#
# Input:
#     sol - internal structure of regular solution (as returned by SolveRecRegular)
#     x - variable
#     Ms - list of EG'-transformed recurrence systems
#
# Output:
#     a user-friendly form of regular solution
#
#######################################################################

    Combine := proc(sol,x,needO)
      local i, j, k, r, ri, res, n, ndx, inds, sbs, vertshifts;

      res := [];
      ndx := 1;
      for k to nops(sol) do
        r := [];
        n := nops(sol[k][2]);

        for j to nops(sol[k][2][1][1]) do
          ri := 0;
          for i to n do
            ri := ri+ln(x)^(n-i)/(n-i)!*(sort(collect(expand(dualnormal(sol[k][2][i][1][j])),x),descending)+
                      `if`(needO,O(x^(sol[k][2][i][3]+1)),0));
          end do;
          r := [op(r),ri]
        end do;
        inds := select(has,sort([op(indets(r)),lexorder]),_c);
        sbs := [];
        for j to nops(inds) do
          sbs := [op(sbs), inds[j]=_c[ndx]];
          ndx := ndx + 1;
        end do;
        r := map(z->x^sol[k][1]*z,subs(sbs,r));
        if res = [] then
          res := r;
        else
          res := res + r;
        end if;
      end do;
      res;
    end;
#######################################################################
################################################################################
# Name  : FormalSolution
# Output:
#     the formal solution of linear differential system of equations
#
################################################################################
FormalSolution := proc()
local indts, Lfun;

    if args[1]::'Matrix' then
        try
            return FormalSolution_theta_form(args);
        catch:
            error ;
        end try;
    end if;
    indts := indets(args[1], 'diff'(anything, anything));
    if indts = {} then
        Lfun := MatCoeffs(args[1],args[2],args[3]);
        try
            return FormalSolution_theta_form(Lfun[1], args[2], op(args[3]),
                          'system_order' = Lfun[2], args[4..-1][]);
        catch:
            error ;
        end try;
    else
        try
            FormalSolution_diff_form(args);
        catch:
            error ;
        end try;
    end if;
end proc:
FormalSolution_theta_form := proc(L::Matrix(square), theta::name, x::name, t::name,
                  {system_order::posint := NULL},
                  {truncate_result::nonnegint := 0},
                  {truncate_system::integer := 0},
                  {solution_dimension::nonnegint := undefined},
                  $)
global _c;
local r, n, L_trunc, t_s, Res, dim, i, j, k, funs, sys, A, dim_expct, ExpParts,
      l, num_exp_part, new_funs, z, ExpParts1, ExpPart, b, val_i, expr, tmp,
      Dx, names, ii, kk, indts;

    if system_order = NULL then
        error
            "the keyword parameter `system_order` (of type posint) is expected";
    end if;
    r := system_order;

    # check the theta name
    if has(theta, _c) then
        error "the 2nd argument is wrong";
    end if;
    # check the independent name
    if has(x, {theta, _c}) then
        error "the 3rd argument is wrong";
    end if;
    # check the parametric name
    if has(t, {_c, x, theta}) then
        error "the 4th argument is wrong";
    end if;

    n := LinearAlgebra:-RowDimension(L);
    if n = 0 then
        error "non empty matrix is expected"
    end if;

    for t_s from truncate_system to truncate_system+1000
    while max(map(degree, expand(convert(L_trunc, set)), theta)) < r do
        try
            L_trunc := Matrix([seq([seq(
                              add(L[i][j](k)*x^k, k = 0 .. t_s+r),
                                                    i = 1 .. n)], j = 1 .. n)]);
        catch:
            error sprintf("impossible to compute %a-truncation of the system",
                                                                           t_s);
        end try;
    end do;
    if t_s > truncate_system+1000 then
        error sprintf("possible, the system is not of %a order or try with greater truncated system", r);
    end if;

userinfo(3, FormalSolution, `start to find regular solutions`);
    try
        Res := EG:-RegularSolution(L, theta, t, truncate_result):
    catch:
        error lasterror;
    end try;
    if Res <> NULL then
        Res := [x = t, simplify(Res, RootOf)];
        dim := nops(indets(Res, _c['integer']));
userinfo(3, FormalSolution, `regular solutions`, Res);
userinfo(3, FormalSolution, `found the `, dim, `-dimension solutions' space`);
    else
        dim := 0;
userinfo(3, FormalSolution, `no regular solutions`);
    end if;

    dim_expct := min(solution_dimension, n*r);
    if dim >= dim_expct then
        return [Res];
    end if;

    _Envdiffopdomain := [Dx, x];

    # choose local names for generated procedures
    names := {t, _c, x, theta};
    names := map(convert, names, 'string');
    for i while convert(expr, 'string') in names do
        expr := cat(expr, i);
    end do;
    for i while convert(ints, 'string') in names do
        ii := cat(ii, i);
    end do;
    kk := k;
    for i while convert(kk, 'string') in names do
        kk := cat(k, i);
    end do;
    # make matrix diffop representation and make valuations of all equations to be 0
    # Matrix([[L[1,1] L[1,2] ... L[1,n]]
    #   ...
    #         [L[n,1] L[n,2] ... L[n,n]]]
    # L[i,j]: k --> a diff operator for yj(x) which is coeff(coeff(L1[1],yj(x)), x, k)
    EG:-Sys := Matrix(n, n);
    for i to n do
        for j to n do
#proc(k)
#option remember;
#local expr, ii, x, y;
#if not k::'integer' then return 'procname'(%a) end if;
#  try
#     expr := add(L[i,j](ii)*x^ii,ii=0..k);
#  catch:
#     error cat(\"impossible to compute \", k, \"-truncation of the system\");
#  end try;
#  expr := EG:-theta2diff(expr, theta, x, y(x));
#  expr := DEtools['de2diffop'](expr, y(x));
#  expr := expand(expr);
#  expr := simplify(coeff(expr, x, k)), 'RootOf');
#  return expr;
#end proc",
            EG:-Sys[i,j] := parse(sprintf(
          "proc(%a)                                                            \
           option remember;                                                    \
           local %a, %a, x, y;                                                 \
              if not %a::'integer' then return 'procname'(%a) end if;          \
              x := _Envdiffopdomain[2];                                        \
              try                                                              \
                  %a := add((%a)(%a)*x^(%a), %a = 0 .. %a);                    \
              catch:                                                           \
                  error cat(\"impossible to compute \", %a,                    \
                                                \"-truncation of the system\");\
              end try;                                                         \
              %a := EG:-theta2diff(%a, %a, x, y(x));                           \
              %a := DEtools['de2diffop'](%a, y(x));                            \
              %a := expand(%a);                                                \
              return simplify(coeff(%a, x, %a), 'RootOf');                     \
           end proc",
           kk,
           expr, ii,
           kk, kk,
           expr, L[i,j], ii, ii, ii, kk,
           kk,
           expr, expr, theta,
           expr, expr,
           expr, expr,
           expr, kk));
        end do;
    end do;

    funs := [seq(y[i](x), i = 1 .. n)];
    sys := [seq(add(DEtools['diffop2de'](
                                    add(EG:-Sys[i,j](k)*x^k, k = 0 .. t_s),
                                               funs[j]), j = 1..n ), i = 1..n)];
    if n > 1 then
        try
            A := convertSysToArray(sys, funs);
        catch:
            error "The truncated system is not full rank";
        end try;
    end if;

    ExpParts := {[x, 0]};
    l := t_s;
    num_exp_part := 1;
    while not(dim >= dim_expct) do
userinfo(3, FormalSolution, `find exponential parts for`, sprintf("%a-truncated system", l));
        if n = 1 then
            ExpParts1 := DEtools['regular_parts'](sys[], funs[], t);
            ExpParts1 := map(el->eval([rhs(el[1]),
                                  indets(el[2], exp('anything'))],
                                                             t = x), ExpParts1);
            ExpParts1 := {map(el->[el[1],
                              `if`(el[2] = {}, 0, op(el[2][1]))], ExpParts1)[]};
        else
            ExpParts1 := ExponentialParts(A*x, x);
        end if;
        ExpParts1 := ExpParts1 minus ExpParts;
        new_funs := [seq(z[i](t), i = 1 .. n)];
        for ExpPart in ExpParts1 do
        # ExpPart = [x^q, alpha[1]/x^kappa[1]+...+alpha[sigma]/x^kappa[sigma]]
            num_exp_part := num_exp_part + 1;

            b := -r*(degree(ExpPart[1],x) - min(0,ldegree(ExpPart[2],x)));
            EG:-thetaSys[num_exp_part] := Matrix(n, n);
            for i to n do
                val_i := infinity;
                for j to n do
                    expr := DEtools['diffop2de'](
                                   add(EG:-Sys[i,j](k)*x^k, k = 0..max(0,-b+r)),
                                                                       funs[j]);
                    expr := PDEtools:-dchange(
                              {x = eval(ExpPart[1], x = t),
                               funs[j] =
                                      exp(eval(ExpPart[2], x = t))*new_funs[j]},
                                                                          expr);
                    expr := expand(expr/exp(eval(ExpPart[2], x = t)));
                    expr := collect(EG:-diff2theta(expr, theta, t,
                                                               new_funs[j]), t);
                    val_i := min(val_i, ldegree(expr, t));
                end do;
                for j to n do
#proc(k)
#option remember;
#local expr, ii, x, y, t, z;
#  if not k::'integer' then return 'procname'(k) end if;
#  if k > truncate_system + 1000 then
#      error "possible, the system is not full rank or try with greater truncated system";
#  end if;
#  expr :=  add(EG:-Sys[i,j](ii)*x^ii,
#                        ii = max(0,(k + val_i + b)/degree(ExpPart[1], x)) ..
#                             max(0,(k + val_i - b + r)/degree(ExpPart[1], x)));
#  expr := DEtools['diffop2de'](expr, y(x));
#  expr := PDEtools:-dchange({x = eval(ExpPart[1], x = t),
#                             y(x) = exp(eval(ExpPart[2], x = t))*z(t)}, expr);
#  expr := expand(expr/exp(eval(ExpPart[2], x = t)));
#  expr := collect(EG:-diff2theta(expr, theta, t, z(t)), t);
#  return simplify(coeff(expr, t, k+val_i), RootOf);
#end proc"
                    EG:-thetaSys[num_exp_part][i,j] := parse(sprintf(
          "proc(k)                                                             \
           option remember;                                                    \
           local expr, i, x, y, %a, z;                                         \
              if not k::'integer' then return 'procname'(k) end if;            \
              if k > (%a)+1000 then                                            \
                  error \"possible, the system is not full rank or try with greater truncated system\"; \
              end if;                                                          \
              x := _Envdiffopdomain[2];                                        \
              expr := add(EG:-Sys[%a,%a](i)*x^i,                               \
                                           i = max(0,floor((k + (%a))/(%a))) ..\
                                               max(0,floor((k + (%a))/(%a)))); \
              expr := DEtools['diffop2de'](expr, y(x));                        \
              expr := PDEtools:-dchange({x = %a, y(x) = exp(%a)*z(%a)}, expr); \
              expr := expand(expr/exp(%a));                                    \
              expr := collect(EG:-diff2theta(expr, %a, %a, z(%a)), %a);        \
              return simplify(coeff(expr, %a, k+(%a)), 'RootOf');              \
           end proc",
              t,
              t_s,
              i, j,
              val_i+b, degree(ExpPart[1], x),
              val_i+r-b, degree(ExpPart[1], x),
              eval(ExpPart[1], x = t), eval(ExpPart[2], x = t), t,
              eval(ExpPart[2], x = t),
              theta, t, t, t,
              t, val_i));


                end do;
            end do;
userinfo(3, FormalSolution, `find regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`);
            try
                tmp := EG:-RegularSolution(EG:-thetaSys[num_exp_part],
                                                     theta, t, truncate_result):
            catch:
                tmp := NULL;
            end try;
            if tmp <> NULL then
                tmp := simplify(tmp, RootOf);
                dim := dim +
                       nops(indets(tmp, _c['integer']))*degree(ExpPart[1], x)*
                       convert(map(el -> degree(op(1, el), _Z),
                                   indets(ExpPart[2], RootOf)), `*`);
                Res := Res,
                       [x = eval(ExpPart[1], x = t),
                        exp(eval(ExpPart[2], x = t))*tmp];
userinfo(3, FormalSolution, `regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`, tmp);
userinfo(3, FormalSolution, `found the `, dim, `-dimension solutions' space`);
            else
userinfo(3, FormalSolution, `no regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`);
            end if;
        end do;
        if dim_expct = undefined or dim >= dim_expct then
            break
        else
            ExpParts := ExpParts union ExpParts1;
            for l from l+1 do
                if l > truncate_system + 1000 then
                  error sprintf("possible, a solution space has \
a lesser dimension then %a or try with greater truncated system", dim_expct);
                end if;
                tmp := [seq(add(DEtools['diffop2de'](EG:-Sys[i,j](l)*x^l, funs[j]),
                                                          j = 1..n), i = 1..n)];
                if tmp = [0$n] then
                    next
                end if;
                sys := zip(`+`, sys, tmp);
                if n > 1 then
                    try
                        A := convertSysToArray(sys, funs);
                    catch:
                        next;
                    end try;
                end if;
                break;
            end do;
        end if;
    end do;
    Res := [Res];
    dim := 0;
    for i to nops(Res) do
        indts := indets(Res[i], _c['integer']);
        Res := subsop(i = eval(Res[i],
                         {seq(indts[j] = _c[dim+j], j = 1..nops(indts))}), Res);
        dim := dim + nops(indts);
    end do;
    return Res;

end proc:
FormalSolution_diff_form := proc(
                  Lfun::{algebraic,`=`,set({algebraic,`=`}),list({algebraic,`=`})},
                  Y::{anyfunc(name),list(anyfunc(name))},
                  t::name,
                  {truncate_result::nonnegint := 0},
                  {truncate_system::integer := 0},
                  {solution_dimension::nonnegint := undefined},
                  $)
global _c;
local x, funs, diff_indts, dot_indts, indts_Sum, indts, dot_part, other_part,
      Dx, r, L1, L1_trunc, inx, n, i, y, lCoef, valL1, cfs, Res, dim, j;

    L1 := Lfun;
    # get dependent variables
    if Y::'anyfunc'('name') then
        x := op(Y);
        funs := [Y];
    elif Y::'list' and nops(Y) > 0 and nops(Y) = nops({Y[]}) then
        x := op(Y[1]);
        if not Y::'list'('anyfunc'('identical'(x))) then
            error "wrong the 2nd argument";
        end if;
        funs := Y;
    else
        error "wrong the 2nd argument";
    end if;

    # check the independent and unknown names
    if has(Y, _c) then
        error "the 2nd argument is wrong";
    end if;

    # check the parametric name
    if has(t, {_c, x, map2(op, 0, funs)[]}) then
        error "the 3rd argument is wrong";
    end if;

    # get system's order
    diff_indts := indets(L1, 'specfunc(anything, diff)');
    diff_indts := select(el -> has(el, funs), diff_indts);
    diff_indts := diff_indts union {funs[]};
    _Envdiffopdomain := [Dx, x];
    try
        r := max(map(el -> degree(DEtools['de2diffop'](el,
                                        (indets(el) intersect {funs[]})[]), Dx),
                                                                   diff_indts));
    catch:
        error "wrong a system's order";
    end try;
    if r = 0 then
        error "wrong a system's order";
    end if;

    # convert the system to the form of list of algebraic
    if Lfun::{'algebraic', `=`} then
        L1 := {Lfun};
    elif Lfun::'list' then
        L1 := convert(Lfun, 'set');
    else
        L1 := Lfun;
    end if;
    L1 := map(el -> `if`(el::`=`, (lhs-rhs)(el), el), L1);
    L1 := convert(L1, 'list');

    # check that all Sums have summation bounds
    #     of type integer..{integer,infinity}
    indts := indets(L1, 'Sum'('anything', 'name' = 'anything'));
    indts_Sum, indts := selectremove(
                             el -> op([2, 2, 1], el)::'integer' and
                                   op([2, 2, 2], el)::{'integer',infinity},
                                                                         indts);
    if indts <> {} then
        error "wrong Sums' bounds";
    end if;

    indts_Sum, indts :=
                     selectremove(el -> op([2, 2, 1], el)::'integer' and
                                        op([2, 2, 2], el)::infinity, indts_Sum);
    if indts <> {} then
        try
            L1 := eval(L1, map(el -> el = eval(el, 'Sum' = 'add'), indts));
        catch:
            error "impossible to compute Sums";
        end try;
    end if;

    # check that all Sums are Sum(anything*x^i, i = integer..infinity)
    if has(map(el -> op(1, el)/x^op([2,1], el), indts_Sum),
                                           {x, t, _c, map2(op, 0, funs)[]}) then
        error "wrong Sums' argument";
    end if;

    # replace all summation indices to a local name
    L1 := eval(L1, map(el -> el = Sum(eval(op(1,el), op([2,1], el) = inx),
                                                           inx = op([2,2], el)),
                       indts_Sum));
    indts_Sum := map(el -> Sum(eval(op(1,el), op([2,1], el) = inx),
                                                           inx = op([2,2], el)),
                       indts_Sum);

    # compute a truncated system
    try
        L1_trunc := eval(L1,
            map(el -> el = eval(
                            'add'(op(1, el),
                                  op([2,1], el) =
                                        op([2,2,1], el) ..
                                        max(truncate_system, op([2,2,1], el)))),
                                                                    indts_Sum));
    catch:
        error sprintf("impossible to compute %a-truncation of the system",
                                                               truncate_system);
    end try;

    # check if the system in the matrix-form
    dot_indts := indets(L1, `.`);
    dot_indts, indts := selectremove(el -> nops(el) = 2 and
                                           op(2, el) in diff_indts and
                                           not has(op(1, el), funs), dot_indts);
    if indts <> {} then
        error "wrong a system's representation";
    end if;

    if has(remove(member, map(el -> op(1, el), dot_indts), indts_Sum),
           indts_Sum) then
       error sprintf("system's coefficients must be either Laurent polynomial in %a, either infinite unevalueted sum", x);
    end if;

    if dot_indts <> {} and nops(L1) = 1 and nops(funs) = 1 then
userinfo(3, FormalSolution, `the matrix-representation is determined`);
      # the system in the form
      # Sum(a[0](i)*x^i, i=0..infinity).Y(x)+
      # Sum(a[1](i)*x^i, i=0..infinity).diff(Y(x),x)
      #                    +...+
      # Sum(a[r](i)*x^i, i=0..infinity).diff(Y(x),x$r)
      #

        L1 := L1[];
        other_part := eval(L1, map(`=`, dot_indts, 0));
        dot_part := L1 - other_part;

        # check that the system is homogeneous
        if eval(dot_part, map(el -> el = 0, dot_indts)) <> 0 or
           eval(other_part, map(el -> el = 0, diff_indts)) <> 0
        then
            error "a homogeneous system is expected"
        end if;

        # check linearity of the system
        if not dot_part::'linear'(dot_indts) or
           other_part <> 0 and not other_part::'linear'(diff_indts) then
            error "the system is not linear";
        end if;

        # check coefficients
        if has(remove(member, {coeffs(other_part, diff_indts)}, indts_Sum),
               indts_Sum) then
            error sprintf("system's coefficients must be either Laurent polynomial in %a, either infinite unevalueted sum", x);
        end if;
        if has({coeffs(dot_part, dot_indts)}, x) then
            error sprintf("system's coefficients must be either Laurent polynomial in %a, either infinite unevalueted sum", x);
        end if;

        # get a system's dimension
        indts := indets(L1_trunc, 'Matrix');
        n := map(LinearAlgebra:-Dimension, indts);
        if nops(n) = 1 and n[1]::'posint' then
            n := n[1];
            L1_trunc, L1 := eval([L1_trunc[], L1],
                {seq(diff(funs[1], x$i) =
                     Vector(diff([seq(y[j](x), j = 1 .. n)], x$i)), i = 1 .. r),
                 funs[1] = Vector([seq(y[j](x), j = 1 .. n)])})[];
            if indets(L1_trunc, `.`) <> {} then
                error sprintf("impossible to compute %a-truncation of the system",
                                                               truncate_system);
            end if;
            L1_trunc := convert(L1_trunc, 'list');
            diff_indts := eval(diff_indts,
                      {seq(diff(funs[1], x$i) =
                           diff([seq(y[j](x), j = 1 .. n)], x$i)[], i = 1 .. r),
                       funs[1] = seq(y[j](x), j = 1 .. n)});
            funs := [seq(y[i](x), i = 1 .. n)];
        elif n = {} then
        # the case of a unique equation
            L1 := [eval(L1, map(el -> el = op(1, el)*op(2,el), dot_indts))];
            L1_trunc := eval(L1_trunc, map(el -> el = op(1, el)*op(2,el),
                                                        indets(L1_trunc, `.`)));
            n := 1;
        else
            error sprintf("impossible to determine a dimension of the %a-truncated system",
                                                               truncate_system);
        end if;


    elif dot_indts = {} then
userinfo(3, FormalSolution, `the set-representation is determined`);
      # the system is in the form
      # [seq(add(Sum(a[0,j,k](i)*x^i, i=0..infinity)*y1(x)+
      #          Sum(a[1,j,k](i)*x^i, i=0..infinity)*diff(y1(x),x)
      #                    +...+
      #          Sum(a[r,j,k](i)*x^i, i=0..infinity)*diff(y1[x],x$r), k=1..n),
      #      j=1..n)]
      #

        # check linearity of the system
        if not L1::'list'('linear'(diff_indts)) then
            error "the system is not linear";
        end if;

        # check that the system is homogeneous
        if {eval(L1, map(el -> el = 0, {diff_indts[], dot_indts[]}))[]} <> {0} then
            error "a homogeneous system is expected"
        end if;

        if has(remove(member, map(coeffs, L1, diff_indts), indts_Sum),
               indts_Sum) then
            error sprintf("system's coefficients must be either Laurent polynomial in %a, either infinite unevalueted sum", x);
        end if;

        # get a system's dimension
        if nops(L1) <> nops(funs) then
            error "the system is not full rank";
        end if;
        n := nops(funs);

    else
        error "wrong a system's representation";
    end if;

    L1_trunc := expand(L1_trunc);

    # check that the truncated leading coefficient is not null
    if {seq(seq(coeff(L1_trunc[j], diff(funs[k], x$r)), k = 1 .. n),
                                                         j = 1 .. n)} = {0} then
        error sprintf("The %a-truncated leading coefficient is null",
                                                               truncate_system);
    end if;

    # check that the truncated system's coefficients are Laurent polynomial in x
    cfs := map(el->[coeffs(el, diff_indts)], L1_trunc);
    if not cfs::'list'('list'('ratpoly'('anything', x))) then
        error "system's coefficients must be Laurent series";
    end if;
    if not cfs::'list'('list'('polynom'('anything', x))) then
        cfs := radnormal(cfs);
        if not denom(cfs)::'list'('list'('monomial'('anything', x))) then
            error "system's coefficients must be Laurent series about 0";
        end if;
    end if;
    cfs := collect(cfs, x);

    # check system's coefficients
    if has(cfs, {t, _c, map2(op, 0, funs)[]}) then
        error sprintf("system's coefficients are deprecated to have names %a",
                                                  {t, _c, map2(op, 0, funs)[]});
    end if;

    if indts_Sum = {} then
    # the case of polynomial coefficients

        try
            return doFSforPolyCf(convert(L1, 'list'),
                                                   funs, t, truncate_result, x);
        catch:
            error lasterror;
        end try;

        end if;
    # get system's valuation
    valL1 := map(el -> min(map(ldegree, el, x)), cfs, x);

    try
        Res := doFormalSolution(L1, funs, t,
                         truncate_result, truncate_system - min(valL1), x, r, n,
                                          valL1, solution_dimension, indts_Sum);
    catch:
        error lasterror;
    end try;

    dim := 0;
    for i to nops(Res) do
        indts := indets(Res[i], _c['integer']);
        Res := subsop(i = eval(Res[i],
                         {seq(indts[j] = _c[dim+j], j = 1..nops(indts))}), Res);
        dim := dim + nops(indts);
    end do;
    return Res;

end proc;
doFSforPolyCf := proc(sys, funs, t, deg0, x)
global _c;
local st, st_total, Res, indts, i, A, n, ExpParts, new_funs, z, ExpPart, sys2, tmp, dim;

    st_total := time():
    userinfo(3, FormalSolution, "start the case of polynomial coefficients");
    if nops(sys) = 1 then
        Res := DEtools['regular_parts'](sys[1], funs[1], t);
        Res := map(el -> [x=rhs(el[1]), rhs(el[2])], Res);
        indts := indets(Res, 'DESol'('anything', 'anything'));
        Res := eval(Res,
             map(el -> el = LinearFunctionalSystems:-ExtendRegularSolution(
                                LinearFunctionalSystems:-RegularSolution(
                                    op(map(convert, el, list))), deg0), indts));
    else
        n := nops(sys);
        st := time():
        try
            A := convertSysToArray(sys, funs);
        catch:
            error "The system is not full rank";
        end try;
        userinfo(3, FormalSolution, "convert to normal system: ", time()-st);
        st:= time():
        ExpParts := eval(ExponentialParts(A*x, x), x = t);
        userinfo(3, FormalSolution, nops(ExpParts), " exponential parts are found: ", time()-st);
        new_funs := [seq(z[i](t), i = 1 .. n)];
        Res := NULL;
        for ExpPart in ExpParts do
            userinfo(3, FormalSolution, "for ", ExpPart);
            sys2 := PDEtools:-dchange(
                         {x = ExpPart[1],
                          seq(funs[i] = exp(ExpPart[2])*new_funs[i], i = 1..n)},
                                                                           sys);
            sys2 := expand(map(`*`, sys2, 1/exp(ExpPart[2])));
            st := time():
            tmp := LinearFunctionalSystems:-RegularSolution(sys2, new_funs);
            userinfo(3, FormalSolution, "regular part of dimension ",
                         nops(indets(tmp, _c['integer'])), " is found:", st-time());
            if {tmp[]} <> {0} then
                Res := Res, [x = ExpPart[1], exp(ExpPart[2])*
                     LinearFunctionalSystems:-ExtendRegularSolution(tmp, deg0)];
            end if;
        end do;
        Res := [Res];
    end if;

    dim := 0;
    for i to nops(Res) do
        indts := indets(Res[i], _c['integer']);
        Res := subsop(i = eval(Res[i],
                         {seq(indts[j] = _c[dim+j], j = 1..nops(indts))}), Res);
        dim := dim + nops(indts);
    end do;

    userinfo(3, FormalSolution, "total time", st_total-time());
    return Res;

end proc:
doFormalSolution := proc(L1, funs, t, deg0, truncate, x, r, n,
                         valL1, sol_dim, indts_Sum)
local z, i, j, new_funs, ii, jj, k, Res, l,
      sys, A, ExpParts, ExpParts1, ExpPart, b, tmp, dim, dim_expct,
      names, expr, sbst, el, kk, val_i, num_exp_part;


    # choose local names for generated procedures
    names := {t} union indets(L1, name) union
             map2(op, 0, indets(L1, 'patindex'('anything'))) union
             map2(op, 0, indets(L1, 'patfunc'('anything'))) minus
             {infinity, 'Sum', 'diff'};
    names := map(convert, names, 'string');
    for i while convert(expr, 'string') in names do
        expr := cat(expr, i);
    end do;
    for i while convert(sbst, 'string') in names do
        sbst := cat(sbst, i);
    end do;
    for i while convert(el, 'string') in names do
        el := cat(el, i);
    end do;
    kk := k;
    for i while convert(kk, 'string') in names do
        kk := cat(k, i);
    end do;
    # make matrix diffop representation and make valuations of all equations to be 0
    # Matrix([[L[1,1] L[1,2] ... L[1,n]]
    #   ...
    #         [L[n,1] L[n,2] ... L[n,n]]]
    # L[i,j]: k --> a diff operator for yj(x) which is coeff(coeff(L1[1],yj(x)), x, k)
    EG:-Sys := Matrix(n, n);
    for i to n do
        for j to n do
#proc(k)
#option remember;
#local expr, el;
#if not k::'integer' then return 'procname'(%a) end if;
#  expr := L1[i,funs[j]<>0];
#  indts := indets(expr, 'Sum'('anything','name' = 'integer'..infinity));
#  try
#      sbst := map(el -> el =
#          `if`(op([2,2,1], el) <= k+val_i,
#                      eval(op(1, el), op([2,1], el) = k+val_i), 0), indts_Sum);
#  catch:
#     error cat(\"impossible to compute \", k+val_i,
#                                                \"-truncation of the system\");
#  end try;
#  if select(el -> has(rhs(el)/x^(k+val_i), names), sbst) <> {} then
#     error cat((k+val_i, \"-coefficients have some names from \",
#                                                        {x, y1, y2,... t, _c});
#  end if;
#  try
#     expr := eval(expr, sbst);
#  catch:
#     error cat("impossible to compute ", k, "-truncation of the system");
#  end try;
#  expr := DEtools['de2diffop'](expr[i], y[j](x));
#  expr := expand(expr);
#  expr := simplify(coeff(expr, x, k+val_i)), 'RootOf');
#  return expr;
#end proc",
            EG:-Sys[i,j] := parse(sprintf(
          "proc(%a)                                                            \
           option remember;                                                    \
           local %a, %a;                                                       \
              if not %a::'integer' then return 'procname'(%a) end if;          \
              %a := %a;                                                        \
              try                                                              \
                  %a := map(%a -> %a =                                         \
                           `if`(op([2,2,1], %a) <= %a+(%a),                    \
                             eval(op(1, %a), op([2,1], %a) = %a+(%a)), 0), %a);\
              catch:                                                           \
                  error cat(\"impossible to compute \", %a,                    \
                                                \"-truncation of the system\");\
              end try;                                                         \
              if select(%a -> has(rhs(%a)/(%a)^(%a+(%a)), %a), %a) <> {} then  \
                  error cat((%a), \"-coefficients have some names from \", %a);\
              end if;                                                          \
              try                                                              \
                  %a := eval(%a, %a);                                          \
              catch:                                                           \
                  error cat(\"impossible to compute \", %a,                    \
                                                \"-truncation of the system\");\
              end try;                                                         \
              %a := DEtools['de2diffop'](%a[%a], %a);                          \
              %a := expand(%a);                                                \
              return simplify(coeff(%a, %a, %a+(%a)), 'RootOf');               \
           end proc",
           kk,
           expr, sbst,
           kk, kk,
           expr, eval(L1, map(`=`, subsop(j = NULL, funs), 0)),
           sbst, el, el,
           el, kk, valL1[i],
           el, el, kk, valL1[i], indts_Sum,
           kk + valL1[i],
           el, el, x, kk, valL1[i], {t, _c, x, map2(op, 0, funs)[]}, sbst,
           kk + valL1[i], convert({t, _c, x, map2(op, 0, funs)[]}, 'string'),
           expr, expr, sbst,
           kk + valL1[i],
           expr, expr, i, funs[j],
           expr, expr,
           expr, x, kk, valL1[i]));
        end do;
    end do;

    sys := [seq(add(DEtools['diffop2de'](
                                    add(EG:-Sys[i,j](k)*x^k, k = 0 .. truncate),
                                               funs[j]), j = 1..n ), i = 1..n)];
    if n > 1 then
        try
            A := convertSysToArray(sys, funs);
        catch:
            error "The truncated system is not full rank";
        end try;
    end if;

    # make matrix theta-representation with 0-valuations of all equations
    # Matrix([[L[1,1] L[1,2] ... L[1,n]]
    #   ...
    #         [L[n,1] L[n,2] ... L[n,n]]]
    # L[i,j]: k --> theta operator for yj(x) which is coeff(coeff(L1[1],yj(x)), x, k)

    thetaSys[1] := Matrix(n, n);
    for i to n do
        val_i := min(seq(ldegree(
            EG:-diff2theta(
              DEtools['diffop2de'](
                 add(EG:-Sys[i,jj](k)*x^k, k = 0..truncate), funs[jj]),
              EG:-theta, x, funs[jj]),
            x),
                   jj = 1..n));
#proc(k)
#option remember;
#local expr, ii;
#  if not k::'integer' then return 'procname'(%a) end if;
#  if k > truncate_system + 1000 then
#      error "possible, the system is not full rank or try with greater truncated system";
#  end if;
#  expr :=  add(EG:-Sys[i,j](ii)*x^ii, ii = k + val_i .. k + val_i+r);
#  expr := DEtools['diffop2de'](expr, y(x));
#  expr := EG:-diff2theta(expand(expr), EG:-theta, x, y(x));
#  return coeff(expr, x, k+val_i);
#end proc"
        for j to n do
            thetaSys[1][i,j] := parse(sprintf(
          "proc(k)                                                             \
           option remember;                                                    \
           local expr, i, x, y;                                                \
              if not k::'integer' then return 'procname'(k) end if;            \
              if k > (%a)+1000 then                                            \
                  error \"possible, the system is not full rank or try with greater truncated system\"; \
              end if;                                                          \
              x := _Envdiffopdomain[2];                                        \
              expr := add(EG:-Sys[%a,%a](i)*x^i, i = k + (%a) .. k + (%a));    \
              expr := DEtools['diffop2de'](expr, y(x));                        \
              expr := EG:-diff2theta(expand(expr), EG:-theta, x, y(x));        \
              return coeff(expr, x, k+(%a));                                   \
           end proc",
              truncate,
              i, j, val_i, val_i+r,
              val_i));
        end do;
    end do;


userinfo(3, FormalSolution, `start to find regular solutions`);
    try
        Res := EG:-RegularSolution(thetaSys[1], 'EG:-theta', t, deg0):
    catch:
        error lasterror;
    end try;
    if Res <> NULL then
        Res := [x = t, simplify(Res, RootOf)];
        dim := nops(indets(Res, _c['integer']));
userinfo(3, FormalSolution, `regular solutions`, Res);
userinfo(3, FormalSolution, `found the `, dim, `-dimension solutions' space`);
    else
        dim := 0;
userinfo(3, FormalSolution, `no regular solutions`);
    end if;

    dim_expct := min(sol_dim, n*r);

    ExpParts := {[x, 0]};
    l := truncate;
    num_exp_part := 1;
    while not(dim >= dim_expct) do
userinfo(3, FormalSolution, `find exponential parts for`, sprintf("%a-truncated system", l));
        if n = 1 then
            ExpParts1 := DEtools['regular_parts'](sys[], funs[], t);
            ExpParts1 := map(el->eval([rhs(el[1]),
                                  indets(el[2], exp('anything'))],
                                                             t = x), ExpParts1);
            ExpParts1 := {map(el->[el[1],
                              `if`(el[2] = {}, 0, op(el[2][1]))], ExpParts1)[]};
        else
            ExpParts1 := ExponentialParts(A*x, x);
        end if;
        ExpParts1 := ExpParts1 minus ExpParts;
        new_funs := [seq(z[i](t), i = 1 .. n)];
        for ExpPart in ExpParts1 do
        # ExpPart = [x^q, alpha[1]/x^kappa[1]+...+alpha[sigma]/x^kappa[sigma]]
            num_exp_part := num_exp_part + 1;

            b := -r*(degree(ExpPart[1],x) - min(0,ldegree(ExpPart[2],x)));
#            b := -(degree(ExpPart[1],x)*r - 1 +
#                   r*(1 - min(0,ldegree(ExpPart[2],x))));
            thetaSys[num_exp_part] := Matrix(n, n);
            for i to n do
                val_i := infinity;
                for j to n do
                    expr := DEtools['diffop2de'](
                                       add(Sys[i,j](k)*x^k, k = 0..max(0,-b+r)),
                                                                       funs[j]);
                    expr := PDEtools:-dchange(
                              {x = eval(ExpPart[1], x = t),
                               funs[j] =
                                      exp(eval(ExpPart[2], x = t))*new_funs[j]},
                                                                          expr);
                    expr := expand(expr/exp(eval(ExpPart[2], x = t)));
                    expr := collect(EG:-diff2theta(expr, EG:-theta, t,
                                                               new_funs[j]), t);
                    val_i := min(val_i, ldegree(expr, t));
                end do;
                for j to n do
#proc(k)
#option remember;
#local expr, ii, x, y, t, z;
#  if not k::'integer' then return 'procname'(k) end if;
#  if k > truncate_system + 1000 then
#      error "possible, the system is not full rank or try with greater truncated system";
#  end if;
#  expr :=  add(EG:-Sys[i,j](ii)*x^ii,
#                        ii = max(0,(k + val_i + b)/degree(ExpPart[1], x)) ..
#                             max(0,(k + val_i - b + r)/degree(ExpPart[1], x)));
#  expr := DEtools['diffop2de'](expr, y(x));
#  expr := PDEtools:-dchange({x = eval(ExpPart[1], x = t),
#                             y(x) = exp(eval(ExpPart[2], x = t))*z(t)}, expr);
#  expr := expand(expr/exp(eval(ExpPart[2], x = t)));
#  expr := collect(EG:-diff2theta(expr, EG:-theta, t, z(t)), t);
#  return simplify(coeff(expr, t, k+val_i), RootOf);
#end proc"
                    thetaSys[num_exp_part][i,j] := parse(sprintf(
          "proc(k)                                                             \
           option remember;                                                    \
           local expr, i, x, y, %a, z;                                         \
              if not k::'integer' then return 'procname'(k) end if;            \
              if k > (%a)+1000 then                                            \
                  error \"possible, the system is not full rank or try with greater truncated system\"; \
              end if;                                                          \
              x := _Envdiffopdomain[2];                                        \
              expr := add(EG:-Sys[%a,%a](i)*x^i,                               \
                                           i = max(0,floor((k + (%a))/(%a))) ..\
                                               max(0,floor((k + (%a))/(%a)))); \
              expr := DEtools['diffop2de'](expr, y(x));                        \
              expr := PDEtools:-dchange({x = %a, y(x) = exp(%a)*z(%a)}, expr); \
              expr := expand(expr/exp(%a));                                    \
              expr := collect(EG:-diff2theta(expr, EG:-theta, %a, z(%a)), %a); \
              return simplify(coeff(expr, %a, k+(%a)), 'RootOf');              \
           end proc",
              t,
              truncate,
              i, j,
              val_i+b, degree(ExpPart[1], x),
              val_i+r-b, degree(ExpPart[1], x),
              eval(ExpPart[1], x = t), eval(ExpPart[2], x = t), t,
              eval(ExpPart[2], x = t),
              t, t, t,
              t, val_i));

                end do;
            end do;
userinfo(3, FormalSolution, `find regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`);
            try
                tmp := EG:-RegularSolution(thetaSys[num_exp_part], EG:-theta, t, deg0):
            catch:
                tmp := NULL;
            end try;

            if tmp <> NULL then
                tmp := simplify(tmp, RootOf);
                dim := dim +
                       nops(indets(tmp, _c['integer']))*degree(ExpPart[1], x)*
                       convert(map(el -> degree(op(1, el), _Z),
                                   indets(ExpPart[2], RootOf)), `*`);
                Res := Res,
                       [x = eval(ExpPart[1], x = t),
                        exp(eval(ExpPart[2], x = t))*tmp];
userinfo(3, FormalSolution, `regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`, tmp);
userinfo(3, FormalSolution, `found the `, dim, `-dimension solutions' space`);
            else
userinfo(3, FormalSolution, `no regular part for`,
            `[`, x=eval(ExpPart[1], x=t), `,`, exp(eval(ExpPart[2], x=t)), `]`);
            end if;
        end do;
        if dim_expct = undefined or dim >= dim_expct then
            break
        else
            ExpParts := ExpParts union ExpParts1;
            for l from l+1 do
                if l > truncate+20 then
                  error sprintf("possible, a solution space has \
a lesser dimension then %a or try with greater truncated system", dim_expct);
                end if;
                tmp := [seq(add(DEtools['diffop2de'](EG:-Sys[i,j](l)*x^l, funs[j]),
                                                          j = 1..n), i = 1..n)];
                if tmp = [0$n] then
                    next
                end if;
                sys := zip(`+`, sys, tmp);
                if n > 1 then
                    try
                        A := convertSysToArray(sys, funs);
                    catch:
                        next;
                    end try;
                end if;
                break;
            end do;
        end if;

    end do;

    return [Res];
end:
################################################################################
convertSysToArray := proc(sys, funs)
local sys0, FirstOrderSys, A, i, j, k, l, m, m1, m2, x, fun_i;

    x := op(funs[1]);
    try
        sys0 := EG:-EG_delta(sys, funs, 'M');
    catch:
        error "It's possible, the equations of the system are dependent.";
    end try;
    try
        FirstOrderSys := DEtools['convertsys']({sys0[]}, {}, {funs[]}, x);
    catch:
        error "It's possible, the the system is not full rank.";
    end try;

    A := Matrix(1 .. nops(FirstOrderSys[1]), 1 .. nops(FirstOrderSys[1]));

    m := Vector(nops(funs));
    for i to nops(funs) do
        m[i] := max(map(el -> nops(DEtools['convertAlg'](el,
                                       (indets(el) intersect {funs[]})[])[1])-1,
                        select(has, map(rhs, FirstOrderSys[2]), funs[i])));
    end do;
    m1 := max(m);
    m := map(el -> [el, Vector[row](el+1)], m);

    m2 := 0;
    for i from 0 to m1 do
        for k to nops(funs) do
            if m[k][1] >= i then
                m[k][2][i+1] := m2+1;
                m2 := m2+1;
            end if;
        end do;
    end do;

    A := Matrix(1 .. nops(FirstOrderSys[1]), 1 .. nops(FirstOrderSys[1]));
    for i to nops(FirstOrderSys[1]) do
        fun_i := (indets(rhs(FirstOrderSys[2][i])) intersect {funs[]})[1];
        m1 := nops(DEtools['convertAlg'](rhs(FirstOrderSys[2][i]), fun_i)[1])-1;
        member(fun_i, funs, 'j');
        for k to nops(FirstOrderSys[2]) do
            fun_i := (indets(rhs(FirstOrderSys[2][k])) intersect {funs[]})[1];
            m2 := nops(DEtools['convertAlg'](rhs(FirstOrderSys[2][k]),
                                                                   fun_i)[1])-1;
            member(fun_i, funs, 'l');
            A[m[j][2][m1+1], m[l][2][m2+1]] :=
                      coeff(rhs(FirstOrderSys[1][i]), lhs(FirstOrderSys[2][k]));
        end do;
    end do;

    return eval(A);

end proc:
################################################################################
################################################################################
Poincare_rank := proc(A1, x)
local A, t;

    for t from 1 to 100 do
        try
            A := map(convert, map(series, map(expand, A1), x, t), 'polynom');
            break;
        catch:
        end try;
    end do;
    if t > 100 then
        error lasterror;
    end if;

    if nargs = 3 and args[3] = "theta" then
        return -min(convert(map(ldegree, A, x), 'set'));
    else
        return -min(convert(map(ldegree, A, x), 'set'))-1;
    end if;
end proc:
################################################################################
Katz_invariant := proc(A1, x)
# x dY = A1(x) Y
# A1(x) = x^(-q)*Sum(A[i]*x^i,i=0..infinity), where q > 0
local n, q, A, T, Airreducible, A_0, r, m, kappa, P_kappa,
      CharPoly, h, i, i0, lst, lambda;

    n := LinearAlgebra:-RowDimension(A1);

    q := Poincare_rank(A1, x, "theta");
    if q <= 0 then
        return 0, 1;
    end if;

    A := map(expand, x^(-q)*convert(map(series, x^q*A1, x, n*q+2), polynom));
    if n = 1 then # y'(x) = (a[-q]/x^q + a[-q+1]/x^(-q+1)+..+a[-1]/x+a[0]+...)*y(x)
                  # ExpPart = exp(int(a[-q]/x^q + a[-q+1]/x^(-q+1)+..+a[-1]/x,x)
error "no tests";
    end if;

    A := map(expand, x^(-q)*convert(map(series, x^q*A1, x, n*q+2), polynom));
    A_0 := map(coeff, A, x, -q);

    Airreducible, T := doMoser(1/x*A, x);
    if q > -min(convert(map(ldegree, map(expand,Airreducible*x), x), 'set')) then
        return procname(x*Airreducible, x);
    end if;

    # Katz-invariant
    r := LinearAlgebra:-Rank(A_0);
    if not (q > n-r or q > r + 1) then
        m := ceil(n/(q-1+r/n));
        kappa, P_kappa := procname(m*eval(A, x = x^m), x);
        return kappa/m, primpart(eval(P_kappa, x = m*x), x);
    end if;

    CharPoly := collect(LinearAlgebra:-CharacteristicPolynomial(A, lambda),
                                                                   [lambda, x]);
    lst := [seq([ldegree(coeff(CharPoly, lambda, i), x), i], i = 0 .. n-1)];
    lst := map(el -> [-el[1]/(n-el[2]), el[1], el[2]], lst);
    kappa := max(map2(op, 1, lst));
    lst := select(el -> el[1] = kappa, lst);
    i0 := min(map2(op, 3, lst));
    P_kappa := tcoeff(coeff(CharPoly, lambda, n), x)*x^(n-i0) +
               add(tcoeff(coeff(CharPoly, lambda, lst[h][3]), x)*
                                          x^(lst[h][3]-i0), h = 1 .. nops(lst));

    return kappa, P_kappa;
end proc:
################################################################################
ExponentialParts := proc(A1, x)
# x dY = A1(x) Y
# A1(x) = x^(-q)*Sum(A[i]*x^i,i=0..infinity), where q > 0
local n, q, d, A, T, Airreducible, A_0, kappa, P_kappa, l, m, R_k, u, v, c,
      A5_3, M, N, B, Res, lst, bs, b, B1, d1, tmp, EValues, M533_1;

    n := LinearAlgebra:-RowDimension(A1);

    q := Poincare_rank(A1, x, "theta");
    if q <= 0 then
        return {[x, 0]};
    end if;

    A := map(expand, x^(-q)*convert(map(series, x^q*A1, x, n*q+2), polynom));
    if n = 1 then
        # y'(x) = (a[-q]/x^q + a[-q+1]/x^(-q+1)+..+a[-1]/x+a[0]+...)*y(x)
        # ExpPart = exp(int(a[-q]/x^q + a[-q+1]/x^(-q+1)+..+a[-1]/x,x)

        return {[x, add(radnormal(-coeff(A[1,1], x, -q+i)/((q-i)*x^(q-i))),
                                                                i = 0 .. q-1)]};
    end if;

    Airreducible, T := doMoser(1/x*A, x);
    if not LinearAlgebra:-Equal(map(expand, Airreducible*x), A) then
        A := map(expand, Airreducible*x);
        q := Poincare_rank(A, x, "theta");
        if q <= 0 then
            return {[x, 0]};
        end if;
    end if;

    kappa, P_kappa := Katz_invariant(A, x);
    l := numer(kappa);
    m := denom(kappa);
    R_k := eval(P_kappa, x = x^(1/m));
    igcdex(l, m, 'u', 'v');

    A5_3 := m*eval(A, x = c*x^m);
    Airreducible, T := doMoser(A5_3/x, x);
    if not LinearAlgebra:-Equal(map(expand, Airreducible*x), A5_3) then
        A5_3 := map(expand, Airreducible*x);
        q := Poincare_rank(A5_3, x, "theta");
        if q <= 0 then
        error " ";
            return {[x, 0]};
        end if;
    end if;

    B, T, d := BlockDiagonalization(A5_3, x, n*q+1);
    M := B[1..d, 1..d];                     # is not singular
    N := eval(B[d+1..-1, d+1..-1], c = 1);  # is nilpotent

    if d < n then
        tmp := procname(N, x);
        Res := map(el-> `if`(el[2]=0,[el[1],el[2]],
                                     [el[1]^m, el[2]]), tmp)[];
        if d = 0 then
            return Res;
        end if;
    else
        Res := NULL;
    end if;


    lst := factors(R_k)[2];
    bs := map(RootOf, map2(op, 1, lst), x);

    for b in bs do
        M533_1 := eval(M, c = b^u);
        Airreducible, T := doMoser(M533_1/x, x);
        if not LinearAlgebra:-Equal(map(expand, Airreducible*x), M533_1) then
            M533_1 := map(expand, Airreducible*x);
            q := Poincare_rank(M533_1, x, "theta");
            if q <= 0 then
                 return {[x, 0]};
            end if;
        end if;
        B1, T, d1 := BlockDiagonalization(
                     M533_1 - m*b^v/x^l*Matrix(d, 'shape' = 'identity'),
                                                                      x, n*q+1);
        if d1 < d then
            tmp := procname(B1[d1+1..-1, d1+1..-1], x);
            Res := Res,
                   map(el-> [b^u*el[1]^m,
                             el[2] - simplify(eval(m*b^v/(l*x^l), x = el[1]),
                                                               RootOf)], tmp)[];
        else # d1 = d
            tmp := procname(B1, x);
            Res := Res,
                   map(el-> [b^u*el[1]^m,
                             el[2] - simplify(eval(m*b^v/(l*x^l), x = el[1]),
                                                               RootOf)], tmp)[];
        end if;
    end do;

    return {Res};

end proc:
################################################################################
BlockDiagonalization := proc(A1, x, Nu::nonnegint)
# x dY = A1(x) Y
# A1(x) = x^(-q)*Sum(A[i]*x^i,i=0..infinity), where q > 0
# Output: 1.B(x) = T^(-1).A1.T - x*T^(-1).dT
#         2.T
#         3.d::nonnegint
#        such that B[0], ..., B[Nu] -- block-diagonal
#               B11[0] -- d x d non-singular
#               B22[0] -- nilpotent
local A, n, q, A_0, EValues, d, P, nu, A_0_11_invert, A_0_11,
      T, AA, BB, HH, TT;

    n := LinearAlgebra:-RowDimension(A1);

    q := Poincare_rank(A1, x, "theta");
    if q <= 0 then
        return A1, LinearAlgebra:-IdentityMatrix(n), 0;
    end if;
    A := map(expand, x^(-q)*convert(map(series, x^q*A1, x, q+Nu+2), polynom));
    A_0 := map(coeff, A, x, -q);
    EValues := convert(LinearAlgebra:-Eigenvalues(A_0), 'list');
    d := nops(remove(Testzero, EValues));
    if d = 0 or d = n then
        if Nu = 0 then
            return A1, LinearAlgebra:-IdentityMatrix(n), d;
        else
            return map(expand, x^(-q)*map(convert, map(series, map(expand,
                 x^q*A1),x, Nu), polynom)), LinearAlgebra:-IdentityMatrix(n), d;
        end if;
    end if;
    P :=map(simplify,
         <Matrix(LinearAlgebra:-ColumnSpace(A_0^n))|
          Matrix([LinearAlgebra:-NullSpace(A_0^n)[]])>,RootOf);
    if not LinearAlgebra:-Equal(P^(-1).A_0.P, A_0) then
        A := map(radnormal,map(expand, x^(-q)*map(convert,
                           map(series, map(expand, x^q*(P^(-1).A1.P)), x, Nu+1),
                                                                     polynom)));
        A := map(simplify, A, RootOf);
        A_0 := map(coeff, A, x, -q);
    else
        P := LinearAlgebra:-IdentityMatrix(n);
    end if;

    if Nu = 0 then
        return P^(-1).A1.P, P, d;
    end if;

    A_0_11 := A_0[1 .. d, 1 .. d];
    A_0_11_invert := A_0_11^(-1);
    T := LinearAlgebra:-IdentityMatrix(n);
    TT[0] := LinearAlgebra:-IdentityMatrix(n);
    BB[0] := A_0;
    for nu from 1 to min(Nu, max(n-d, d)*q+1) do
        AA[nu] := map(coeff, A, x, -q+nu);
        if nu-q < 0 then
            TT[nu-q] := LinearAlgebra:-ZeroMatrix(n);
        end if;
        HH[nu] := -AA[nu] + add(TT[j].BB[nu-j] - AA[nu-j].TT[j], j = 1 .. nu-1)+
                                                                (nu-q)*TT[nu-q];
        BB[nu] := map(radnormal,
                  <<-HH[nu][1 .. d, 1 .. d] |
                                           LinearAlgebra:-ZeroMatrix(d, n-d)>,
                   <LinearAlgebra:-ZeroMatrix(n-d, d) |
                                                 -HH[nu][d+1 .. n, d+1 .. n]>>);
        TT[nu] := map(radnormal,
                  <<LinearAlgebra:-ZeroMatrix(d, d) |
                                      A_0_11_invert.HH[nu][1 .. d, d+1 .. n]>,
                   <-HH[nu][d+1 .. n, 1 .. d].A_0_11_invert |
                                         LinearAlgebra:-ZeroMatrix(n-d, n-d)>>);
    end do;

    T := add(x^nu * TT[nu], nu = 0 .. min(Nu, max(n-d, d)*q+1));
    T := P.T;

    return add(x^(nu-q)*BB[nu], nu = 0 .. min(Nu, max(n-d, d)*q+1)),
           copy(T), d;
end proc:
################################################################################
doMoser := proc(A1, x)
local n, A, r, A_0, A_1, EValues, dim_M, theta_A_lambda, lambda, J_0, T, Res,
      ni, li, ci, n_i, i, j, s, d, L_A_lambda, L_A_0,
      q, v, u, P, S;


    n := LinearAlgebra:-RowDimension(A1);
    r := Poincare_rank(A1, x);
    if r <= 0 then
        return copy(A1), LinearAlgebra:-IdentityMatrix(n);
    end if;

    A := map(expand, x^(-r-1)*convert(map(series, x^(r+1)*A1, x, n*r+3), polynom));

    A_0 := map(coeff, A, x, -r-1);

    EValues := convert(LinearAlgebra:-Eigenvalues(A_0), 'set');
    if EValues <> {0} then
        A, T, dim_M := BlockDiagonalization(A1*x, x, 0);
        A := map(expand, A*(1/x));
        Res := procname(A[dim_M+1..n, dim_M+1..n], x);
        T^(-1).A1.T-T^(-1).map(diff,T,x);
        P := <<LinearAlgebra:-IdentityMatrix(dim_M) |
               LinearAlgebra:-ZeroMatrix(dim_M, n-dim_M)>,
              <LinearAlgebra:-ZeroMatrix(n-dim_M, dim_M) | Res[2]>>;
        return P^(-1).A.P-P^(-1).map(diff,P,x), copy(T.P);
    end if;

    A_1 := map(coeff, A, x, -r);

    theta_A_lambda := eval(radnormal(x^LinearAlgebra:-Rank(A_0)*
                    LinearAlgebra:-CharacteristicPolynomial(A_0/x+A_1, lambda)),
                                                                         x = 0);
    if theta_A_lambda <> 0 then
        return copy(A1), LinearAlgebra:-IdentityMatrix(n);
    end if;

    J_0, T := LinearAlgebra:-JordanForm(A_0, 'output' = ['J', 'Q']);
    if not LinearAlgebra:-Equal(A_0, J_0) then
        A := T^(-1).A1.T-T^(-1).map(diff, T, x);
        Res := procname(A, x);
        return copy(Res[1]), copy(T.Res[2]);
    end if;

    # Get dimesions of Jordan blocks
    ni, li, ci := [], [], [];
    for i to n do
        ci := [ci[], i];
        for n_i to n - convert(ni, `+`)
                           while convert(A_0[i-1+n_i], 'set') <> {0} do  end do;
        ni := [ni[], n_i];
        i := i-1 + n_i;
        li := [li[], i];
    end do;

    if sort(ni, `>`) <> ni then
        error "no tests";
    end if;

    s := nops(select(`=`, ni, 1));
    d := nops(ni) - s;
    L_A_lambda := Matrix([seq([seq(A_1[li[i], ci[j]], j = 1 .. nops(ni))],
                                                          i = 1 .. nops(ni))]) -
                  LinearAlgebra:-DiagonalMatrix([0$d, lambda$s]);
    if LinearAlgebra:-Determinant(L_A_lambda) <> 0 then
        error "it's impossible if theta_A_lambda = 0"
    end if;

    # Compute a constant transformation C: L(C[A],lambda) has structure (7)
    L_A_0 := eval(L_A_lambda, lambda = 0);

    q := Lemma2_1(L_A_0, lambda, d, s, 'v');
    if assigned(v) then
        u := <seq([v[i], `$`(0, ni[i]-1)][], i = 1 .. d+s)>;
        P := <<LinearAlgebra:-IdentityMatrix(n-q-1),
                   LinearAlgebra:-ZeroMatrix(q+1,n-q-1)> | u |
                   LinearAlgebra:-ZeroMatrix(n-q,q),
                   LinearAlgebra:-IdentityMatrix(q)>;
        if not LinearAlgebra:-Equal(P, Matrix(n, 'shape' = 'identity')) then
            A := P^(-1).A1.P;
            Res := procname(A, x);
            return copy(Res[1]), copy(P.Res[2]);
        else
        end if;
    end if;

    S := LinearAlgebra:-DiagonalMatrix([
           seq([LinearAlgebra[IdentityMatrix](ni[i]-1), x][], i = 1 .. d),
           seq(x, i = 1 .. s-q),
           LinearAlgebra[IdentityMatrix](q)]);
    A := S^(-1).A1.S-S^(-1).map(diff, S, x);
    Res := procname(A, x);
    return copy(Res[1]), copy(S.Res[2]);

end proc:
################################################################################
Lemma2_1 := proc(L_A_0, lambda, d, s, v)
local q, flag, L11, L12, L21, L22, L13, L23, expr, slv, i, C;

    L11 := L_A_0[1 .. d, 1 .. d];

    flag := true;
    for q from 1 to s while flag do
        L13, L23 := L_A_0[1 .. d, -q .. -1], L_A_0[d+1 .. -1-q, -q .. -1];
        flag := LinearAlgebra:-Equal(L13, LinearAlgebra:-ZeroMatrix(d, q)) and
                LinearAlgebra:-Equal(L23, LinearAlgebra:-ZeroMatrix(s-q, q));
    end do;
    if not flag then
        q := q - 2;
    else
        q := q - 1;
    end if;

    L12 := L_A_0[1 .. d, d+1 .. -1-q];
    L21, L22 := L_A_0[d+1 .. -1-q, 1 .. d], L_A_0[d+1 .. -1-q, d+1 .. -1-q];

    if LinearAlgebra:-Rank(<L11, L21>) + s - q =
                              LinearAlgebra:-Rank(<<L11, L21>|<L12, L22>>) then
        return q;
    end if;

    expr := L_A_0.<seq(C[j], j = 1 .. d+s)>;
    slv := {};
    for i from d+s-q by -1 to d+1 while slv = {} do
        slv := solve(convert(eval(expr, C[i] = 1), 'set'));
    end do;
    if slv <> {} then
        i := i + 1;
    end if;
    v := eval(eval(<seq(C[j], j = 1 .. d+s)>, slv union {C[i] = 1}),
                                                 {seq(C[j] = 0, j = 1 .. d+s)});
    return q;
end proc:
###################################################################
diff2theta := proc (expr, theta, x, fun)
option remember;
local tmp, n;
    tmp := DEtools[convertAlg](expr, fun, x);
    n := nops(tmp[1])-1;
    if n = 0 then
        return tmp[1][-1]+tmp[2];
    end if;
    return expand(tmp[1][-1]*theta^n/x^n) +
           procname(expr - EG:-theta2diff(tmp[1][-1]*theta^n/x^n,
                                          theta, x, fun),
                    theta, x, fun);
end proc:
theta2diff := proc (expr, theta, x, fun)
option remember;
local tmp1, tmp2, i;

    if expr = theta then
        return x*(diff(fun, x));
    elif not has(expr, theta) then
        return expr*fun;
    elif expr::{`+`} then
        return map(procname, expr, theta, x, fun);
    elif expr::`*` then
        tmp1, tmp2 := selectremove(has, expr, theta);
        if tmp1::`*` then
            return map(`*`, map(procname, expand(tmp1), theta, x, fun), tmp2);
        else
            return expand(tmp2*procname(tmp1, theta, x, fun));
        end if
    elif expr::(identical(theta)^posint) then
        return expand(procname(theta, theta, x,
                               procname(theta^(op(2, expr)-1), theta, x, fun)));
    elif expr::'piecewise' then
        if nops(expr)::'odd' then
            return piecewise(seq([op(i*2-1,expr),
                                  procname(op(i*2,expr), theta, x, fun)][],
                                 i=1..(nops(expr)-1)/2),
                             procname(op(-1,expr), theta, x, fun));
        else
            return piecewise(seq([op(i*2-1,expr),
                                  procname(op(i*2,expr), theta, x, fun)][],
                                 i=1..nops(expr)/2));
        end if;
    else
        error "unknown expression";
    end if;
end proc:
################################################################################

################################################################################
Xi := proc(ex,x)
	local sumpart, sumpartcoef, polpart, summand, sumfrom, sumto, other, sumndx, z;
	if op(0,ex)='Sum' or (type(ex,`*`) and op(0,op(2,ex))='Sum') then
		sumpart:=ex
	elif type(ex,`+`) then
		sumpart := select(has,ex,Sum)
    else
        sumpart := 0;
	end if;
    sumpartcoef := 1;
    if sumpart=NULL then
        sumpart := 0;
    elif type(sumpart,`*`) then
		sumpartcoef := op(1,sumpart);
		sumpart := op(2,sumpart);
	end if;
	if (sumpart<>0) and not type(sumpart,function(anything)) then
		error("only one Sum is expected in the series expression");
	end if;
	polpart := normal(ex-sumpartcoef*sumpart);
    if sumpart<>0 then
	   summand := sumpartcoef*op(1,sumpart);
	   sumndx := op(1,op(2,sumpart));
	   sumfrom := op(1,op(2,op(2,sumpart)));
	   sumto := op(2,op(2,op(2,sumpart)));
	   if not has(summand,x^sumndx) and (summand<>0) then
		  error("Summand should be in powers of x");
	   end if;
	   other := coeff(summand,x^sumndx);
    end if;
    if polpart<>0 and sumpart<>0 then
		unapply(coeff(polpart,x,z)+`if`(z>=sumfrom,1,0)*subs(sumndx=z,other),z);
    elif polpart=0 and sumpart<>0 then
		unapply(`if`(z>=sumfrom,1,0)*subs(sumndx=z,other),z);
    elif polpart<>0 and sumpart=0 then
		unapply(coeff(polpart,x,z),z);
    else
		0
    end if;
end:
################################################################################

################################################################################
MatCoeffs := proc(sys,theta,var)
	local opers, op0, op1, op2, order, orderi, cffs, i, z, w;

	if not type(sys,`+`) and not type(sys,`.`) then
		error("1 the system should be given as a sum of dot multiplied matrices and functions")
	end if;
	if type(sys,`+`) then
		opers := [op(sys)];
	else
		opers := [sys];
	end if;
	order := -1;
	cffs := [];
	for i to nops(opers) do
		op0 := 1;
		if type(opers[i],`*`) then
			opers[i] := -opers[i];
			op0 := -1;
		end if;
		if not type(opers[i],`.`) then
			error("2 the system should be given as a sum of dot multiplied matrices and functions")
		end if;
		if nops(opers[i])<>2 then
			error("3 the system should be given as a sum of dot multiplied matrices and functions")
		end if;
		op1, op2 := op(opers[i]);
		if type(op1, Matrix) then
			if not type(op2, function) then
				error("4 the system should be given as a sum of dot multiplied matrices and functions")
			end if;
		else
			error("6 the system should be given as a sum of dot multiplied matrices and functions")
		end if;
		if op2=var then
			orderi := 0;
		elif op(0,op2)=theta then
			if nops(op2)>3 and nops(op2)<=2 then
				error("7 the functions in systems should be either functions to solve for or its deriveties in theta");
			else
				if (op(1, op2)<>var) and (op(2,op2)<>op(1,var)) then
					error("8 the functions in systems should be either functions to solve for or its deriveties in theta");
				end if;
				if nops(op2)=2 then
					orderi := 1;
				elif not type(op(3,op2),nonnegint) then
					error("9 the functions in systems should be either functions to solve for or its deriveties in theta");
				else
					orderi := op(3,op2);
				end if;
			end if;
		else
			error("10 the functions in systems should be either functions to solve for or its deriveties in theta");
		end if;
		order := max(order, orderi);
		cffs := [[orderi,copy(op1),op0], op(cffs)];
	end do;
    [map(unapply,`+`(seq(map(z->cffs[i][3]*Xi(z,op(1,var))(w)*theta^cffs[i][1],cffs[i][2]),i=1..nops(cffs))),w), order];
end:
################################################################################

end module:

protect('EG'):
#savelib('EG'):
