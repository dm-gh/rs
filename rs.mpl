read "lib/eg.mpl"; 
RS := module () 
	option package;
	local InducedSys, IndicalEq, UniversalDenom; 
	export RationalSolution;  

	InducedSys := proc (sys, independant_var) 
		local A, B, rules, Result; 

		A := add(`~`[`*`](sys[i], delta^(i-1)), i = 1 .. nops(sys)); 
		B := subs(delta = (n+1)*En+1, independant_var = n+En1, A); 
		rules := curry(applyrule, [En^(i::integer)*C(n) = C(n+i), En1^(i::integer)*C(n) = C(n-i)]); 
		Result := map(rules, map(collect, `~`[`*`](simplify(B, {En*En1 = 1}), ` $`, C(n)), [En, En1])); 
		Result 
	end proc; 

	IndicalEq := proc(sys, independant_var) 
		local induced, prepSys, prepVars, inducedEGSysTemp, egSys, l, leadMat, det; 

		induced := InducedSys(sys, independant_var); 
		prepSys := convert(add(seq(
			subs(C = C[i], LinearAlgebra:-Column(induced, i)), 
			i = 1..LinearAlgebra:-ColumnDimension(induced)
		)), list); 
		prepVars := [seq(C[i](n), i = 1 .. LinearAlgebra:-ColumnDimension(induced))]; 
		egSys := EG:-EG_sigma(prepSys, prepVars, 'lead', inducedEGSysTemp); 
		l := max(map(o -> o-n, map(op, select(has, indets(egSys), C))));
		leadMat := inducedEGSysTemp[1][
			1..LinearAlgebra:-ColumnDimension(induced), 
			1..LinearAlgebra:-RowDimension(induced)
		]; 
		det := LinearAlgebra:-Determinant(leadMat); 
		return subs(n=n-l, det);
	end proc; 	

	UniversalDenom := proc(V, W, independant_var)
		local H, U, V_new, W_new, N, h;

		H := LRETools:-dispersion(V, W, independant_var);
		if H = FAIL then
			return 1;
		end if;

		H := sort(convert(H, list), `>`);
		U := 1;
		V_new := V;
		W_new := W;

		for h in H do
			N := gcd(V_new, subs(independant_var=independant_var+h, W_new));
			V_new := simplify(V_new / N);
			W_new := simplify(W_new / subs(independant_var=independant_var-h, N));
			U := U * product(subs(independant_var=independant_var-j, N), j=0..h);
		end do;

		return U;
	end proc;

	RationalSolution := proc(sys, independant_var)
		local indical_eq, int_ind_roots, lambda, prepSys1, prepSys2, prepVars, 
			lEmbracingSys, lEmbracingSysTable, tEmbracingSys, tEmbracingSysTable,
			r, V, W, h, omega, U, d, U_1, transformedSys1, transformedSys2, transformedVars,
			polySols, ratSols;

		indical_eq := IndicalEq(sys, independant_var);
		int_ind_roots := select(type, [solve(indical_eq)], integer);
		if int_ind_roots = [] then
			print("STOP 1");
			return [];
		end if;
		lambda := max(int_ind_roots);

		# print("indical_eq = ", indical_eq, "int_ind_roots = ", int_ind_roots, "lambda = ", lambda);

		prepSys1 := add(sys[i]*y(independant_var+i-1), i = 1 .. nops(sys));
		prepSys2 := convert(add(seq(
			subs(y = y[i], LinearAlgebra:-Column(prepSys1, i)),
			i = 1 .. LinearAlgebra:-ColumnDimension(prepSys1)
		)), list);
		prepVars := [seq(y[i](independant_var), i = 1 .. LinearAlgebra:-ColumnDimension(prepSys1))];
		lEmbracingSys := EG:-EG_sigma(prepSys2, prepVars, 'lead', lEmbracingSysTable); 
		tEmbracingSys := EG:-EG_sigma(prepSys2, prepVars, 'trail', tEmbracingSysTable); 
		r := max(map(o -> o-independant_var, map(op, select(has, indets(lEmbracingSys), y))));

		V := subs(
			independant_var=independant_var-r, 
			LinearAlgebra:-Determinant(lEmbracingSysTable[1][
				1..LinearAlgebra:-ColumnDimension(prepSys1), 
				1..LinearAlgebra:-RowDimension(prepSys1)
			])
		); 
		W := LinearAlgebra:-Determinant(tEmbracingSysTable[1][
			-LinearAlgebra:-ColumnDimension(prepSys1)..-1, 
			-LinearAlgebra:-RowDimension(prepSys1)..-1
		]); 
		h := LRETools:-dispersion(V, W, independant_var, 'maximal');
		omega := min({degree(V), degree(subs(independant_var=independant_var+h, W))});

		if lambda + omega < 0 then
			print("STOP 2");
			return [];
		end if;
		# print("omega = ", omega);

		U := UniversalDenom(V, W, independant_var);
		d := lambda + degree(U, independant_var);

		if d < 0 then
			print("STOP 3");
			return [];
		end if;

		# print("U = ", U, "d = ", d);

		U_1 := simplify(1/U);
		transformedSys1 := map(
			curry(applyrule, y(independant_var+n::integer) = 
				subs(independant_var=independant_var+n, U_1) * z(independant_var+n)
			),
			prepSys1
		);
		transformedSys2 := convert(add(seq(
			subs(z = z[i], LinearAlgebra:-Column(transformedSys1, i)), 
			i = 1 .. LinearAlgebra:-ColumnDimension(transformedSys1)
		)), list);
		transformedVars := [seq(z[i](independant_var), i = 1 .. LinearAlgebra:-ColumnDimension(transformedSys1))];

		polySols := LinearFunctionalSystems:-PolynomialSolution(transformedSys2, transformedVars, 'degree'=d);
		ratSols := map(sol -> simplify(U_1 * sol), polySols);

		return ratSols;
	end proc; 

end module;
