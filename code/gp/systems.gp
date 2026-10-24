\\ The two linear systems printed in Section 4 (proofs of Theorems 4.4 and 4.5), checked as polynomial identities.
\\ theta acts on independent variables through Ramanujan's equations (Theorem 4.1 and its image under V) and
\\ theta g = E g; each line prints the difference of the two sides, which must be 0.
\\ Run: gp -q systems.gp < /dev/null > systems.out

\\ Level 3. Variables: p1, q1, r1 = E2, E4, E6; p3, q3, r3 = their images under V; g. A is the series E.
vars = [p1, q1, r1, p3, q3, r3, g];
dv = [(p1^2 - q1)/12, (p1*q1 - r1)/3, (p1*r1 - q1^2)/2, (p3^2 - q3)/4, p3*q3 - r3, 3*(p3*r3 - q3^2)/2, g*(3*p3 - p1)/2];
th(f) = sum(k = 1, 7, deriv(f, vars[k])*dv[k]);
A = (3*p3 - p1)/2;
e1 = (1 + g)*q1 - A^2*(1 + 9*g); e2 = 9*(1 + g)*q3 - A^2*(9 + g);
e3 = (1 + g)^2*r1 - A^3*(1 - 18*g - 27*g^2); e4 = 27*(1 + g)^2*r3 - A^3*(27 + 18*g - g^2);
E = [e1, e2, e3, e4];
{N = [((5*g + 9)*p1 + 3*(3*g - 1)*p3)/24, (9*g + 1)*A/12, -1/3, 0;
  -(g + 9)*A/12, (-(13*g + 9)*p1 + 3*(21*g + 17)*p3)/24, 0, -1/3;
  -(45*g^2 + 62*g + 9)*A^2/8 - (1 + g)*e1/2, -(27*g^2 + 18*g - 1)*A^2/8, ((1 - g)*p1 + 6*g*p3)/2, 0;
  (g^2 - 18*g - 27)*A^2/8, -(9*g^2 + 62*g + 45)*A^2/8 - (1 + g)*e2/2, 0, (-2*g*p1 + 3*(3*g + 1)*p3)/2];}
for (i = 1, 4, print("level 3, (1+g) theta delta_", i, " - (N delta)_", i, ": ", simplify((1 + g)*th(E[i]) - sum(j = 1, 4, N[i, j]*E[j]))));
N0 = substvec(N, [p1, p3, g, q1, q3, r1, r3], [1, 1, 0, 1, 1, 1, 1]);
print("level 3, N(0) = ", N0);
print("level 3, det(n I - N(0)) = ", factor(matdet(n*matid(4) - N0)));

\\ The derivative of E modulo the first two identities of Theorem 4.4 (q1, q3 eliminated through e1, e2).
tE = subst(subst(6*(1 + g)*th(A) - A*((1 + g)*p1 + (3*g - 1)*A), q1, A^2*(1 + 9*g)/(1 + g)), q3, A^2*(9 + g)/(9*(1 + g)));
print("6(1+g) theta E - E((1+g)E2 + (3g-1)E): ", simplify(tE));

\\ Level 9. Variables: P9 = V^2 E2, u = V E, W, a = E, g. V E2 and E2 are written through 2E = 3 V E2 - E2.
\\ theta of u from V applied to the identity above, with (1 - W^3)(1 + Vg) = 1 (Theorem 4.5 (b)); theta W = u (1 - W^3) W.
kill(vars); kill(A); kill(N);
vars = [P9, u, W, a, g];
VE2 = 3*P9 - 2*u; E2 = 3*VE2 - 2*a;
dv = [tP9, u*(VE2 + (4*W^3 - 1)*u)/2, u*(1 - W^3)*W, a*((1 + g)*E2 + (3*g - 1)*a)/(6*(1 + g)), a*g];
th(f) = sum(k = 1, 5, deriv(f, vars[k])*dv[k]);
Vg = W^3/(1 - W^3);
print("V of the identity for theta E, times 2(1 - W^3): ", simplify(2*(1 - W^3)*(6*(1 + Vg)*th(u)/3 - u*((1 + Vg)*VE2 + (3*Vg - 1)*u))));
K = a - u*(1 + 2*W)^2; L = (1 - W)^3*g - 9*W*(1 + W + W^2);
w = 6*(1 + g)*(1 + 2*W)^3;
N11 = (1 + g)*(9*P9*(1 + 2*W)^3 + 3*(32*u*W^5 + 32*u*W^4 + (40*u + 4*K)*W^3 + 16*u*W^2 + (6*K - 8*u)*W - 4*u - K));
N12 = 4*a^2; N21 = 54*(1 + g)*(1 + 2*W)^3*W*(1 + W + W^2); N22 = 6*(1 + g)*(1 + 2*W)^3*(a - 3*u*W*(1 + W + W^2));
print("level 9, w theta K - N11 K - N12 L: ", simplify(w*th(K) - N11*K - N12*L));
print("level 9, w theta L - N21 K - N22 L: ", simplify(w*th(L) - N21*K - N22*L));
N9 = substvec([N11, N12; N21, N22], [P9, u, W, a, g], [1, 1, 0, 1, 0]);
print("level 9, w(0) = ", substvec(w, [W, g], [0, 0]), ", N(0) = ", N9);
d9 = matdet(6*n*matid(2) - N9);
print("level 9, det(6n I - N(0)) = ", content(d9), " * ", factor(d9/content(d9)));
