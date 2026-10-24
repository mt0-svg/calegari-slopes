\\ The numbers printed in the paper that no Lean declaration states, recomputed from the definitions of
\\ Section 1 of the paper (q-expansions from divisor sums, F from its numerator and denominator, Loeffler's
\\ formulas for A, B, D). Run: gp -q numbers.gp < /dev/null > numbers.out
default(seriesprecision, 20);
P = 12;

\\ slopes sigma_i = 2i + 2 v_3((2i)!/i!) and their partial sums
sig(i) = 2*i + 2*valuation((2*i)!/i!, 3);
print("sigma(1..12) = ", vector(12, i, sig(i)));
print("Sigma(1..8) = ", vector(8, n, sum(i = 1, n, sig(i))));

\\ q-expansions
ser(f) = sum(n = 1, P, f(n)*q^n) + O(q^(P+1));
E2 = 1 - 24*ser(n -> sigma(n, 1));
E4 = 1 + 240*ser(n -> sigma(n, 3));
E6 = 1 - 504*ser(n -> sigma(n, 5));
Dl = (E4^3 - E6^2)/1728;
jinv = Dl/E4^3;
print("1/j = ", jinv + O(q^5));
V3(f) = subst(f, q, q^3);
Ec = (3*V3(E2) - E2)/2;
print("E (level 3 weight 2) = ", Ec + O(q^5));

\\ Sol(b, c): y_0 = 0, y_1 = c, (n - 1) y_n = sum_{k=1}^{n-1} b_k y_{n-k}
sol(b, c, N) = {
  my(y = vector(N), bb = vector(N, k, polcoef(b, k, q)));
  y[1] = c;
  for (n = 2, N, y[n] = sum(k = 1, n - 1, bb[k]*y[n - k])/(n - 1));
  sum(n = 1, N, y[n]*q^n) + O(q^(N+1));
}
g = sol(Ec, 27, P);
print("g = ", g + O(q^5));
b = V3(Ec/(1 + g));
W = sol(b, 3, P);
print("W = ", W + O(q^11));

\\ u_ij: coefficients of F = N/Q
Nxy = 90*x*y + 324*x^2*y + 648*x*y^2 + 243*x^3*y + 486*x^2*y^2 + 729*x*y^3;
Qxy = 1 - 270*x*y - 972*x*y*(x + y) - 729*x*y*(x^2 + x*y + y^2);
Fser = Nxy*sum(k = 0, 8, (1 - Qxy)^k);
u(i, j) = polcoef(polcoef(Fser, i, x), j, y);
print("column 1 of u: ", vector(3, i, u(i, 1)));
print("column 2 of u: ", vector(6, i, u(i, 2)));
print("u_12 = ", u(1, 2), ", u_21 = ", u(2, 1));

\\ Loeffler's factors
r(t, i) = (3*i + 3*t)!*i!/(3^t*(3*i)!*(i + t)!);
muL(i, k, t) = {if (i - k + 2*t < 0 || k - i - t < 0 || i - t < 0, return(0));
  2*k*i!*k!*(2*i + 2*t)!*(2*i + t - 1)!/((i + k)!*(i - k + 2*t)!*(2*i)!*(k - i - t)!*(i - t)!*(i + t)!)};
B(i, k) = sum(t = 0, i, 3^(2*t)*muL(i, k, t)/r(t, i));
A(i, k) = k/i*B(k, i);
D(k) = 3^(3*k)*(6*k)!*(2*k)!*k!/(2*(3*k)!^3);
print("D_1, D_2, D_3 = ", [D(1), D(2), D(3)], ", valuations ", [valuation(D(1),3), valuation(D(2),3), valuation(D(3),3)]);
print("row 1 of B: ", vector(3, k, B(1, k)));
print("row 2 of B: ", vector(6, k, B(2, k)));


\\ the first coefficients used in the base cases of Section 4
print("E2 = ", E2 + O(q^4));
print("E4 = ", E4 + O(q^4));
print("E6 = ", E6 + O(q^4));

\\ the base columns of Section 5: S_ij = i u_ij and V_ij = sum_p p D_p B_pi B_pj for j = 1, 2
V(i, j) = sum(p = 1, min(i, j), p*D(p)*B(p, i)*B(p, j));
print("S(i,1), i = 1..3: ", vector(3, i, i*u(i, 1)), "  V(i,1): ", vector(3, i, V(i, 1)));
print("S(i,2), i = 1..6: ", vector(6, i, i*u(i, 2)), "  V(i,2): ", vector(6, i, V(i, 2)));
print("D_1 B_{1,3} = ", D(1)*B(1, 3), ", D_2 B_{2,6} = ", D(2)*B(2, 6));

\\ Section 8: the first superdiagonal of B, the first subdiagonal of A, and the pair (2, 4)
print("B_{i,i+1} - 36 i (i+1)^2/((3i+1)(3i+2)), i = 1..50: ", vecmax(vector(50, i, abs(B(i, i + 1) - 36*i*(i + 1)^2/((3*i + 1)*(3*i + 2))))));
print("A_{i+1,i} - 36 i^2 (i+1)/((3i+1)(3i+2)), i = 1..50: ", vecmax(vector(50, i, abs(A(i + 1, i) - 36*i^2*(i + 1)/((3*i + 1)*(3*i + 2))))));
print("mu(2,4,1), r_1(2), mu(2,4,2), r_2(2) = ", [muL(2, 4, 1), r(1, 2), muL(2, 4, 2), r(2, 2)]);
print("B_24 = ", B(2, 4), ", A_42 = ", A(4, 2), ", valuations ", [valuation(B(2, 4), 3), valuation(A(4, 2), 3)]);
