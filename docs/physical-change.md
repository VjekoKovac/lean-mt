# Returning to the physical coordinates in Proposition 3.1

The cap calculation yields a lower bound for the integral of $|Ef(Ay)|^2w(y)$, where $A$ is the adjoint of the linear part of the frequency change. In the original physical coordinates use the weight $w'(x)=w(A^{-1}x)$. The change $x=Ay$ gives
$$
\int |Ef(x)|^2 w'(x)\,dx
 = |\det A|\int |Ef(Ay)|^2w(y)\,dy .
$$
`MT.weightedMass_inverse_weight` gives this identity for the extended nonnegative integral. It uses mathlib's Haar-measure determinant formula and change of variables by a measurable equivalence. The determinant occurs in absolute value, so orientation-reversing changes are included.

If $w$ is admissible in the open ball of radius $R$ and continuous, then $w'$ is admissible in the open ball of radius $\|A\|R$. To see the X-ray estimate, take any unit direction $v$ and any offset $b$. The original line parameter $t$ becomes $s=\|A^{-1}v\|t$, and the transformed direction $A^{-1}v/\|A^{-1}v\|$ has norm one. The integral gains a factor $1/\|A^{-1}v\|≤\|A\|$. Lemma 3.5 controls every offset, including the potentially nonperpendicular offset $A^{-1}b$. Taking the essential supremum on the sphere yields the upper bound. The weight of the paper is continuous and takes value $|B|^2>0$ at the origin, which also gives strict positivity for the transformed X-ray norm.

`MT.inverse_counterWeight_estimates` collects the bounds for the paper's actual finite sum of tents and exponentials. It gives continuity, admissibility with radius $\|A\|(\sqrt{d+1}+1)T$, and an X-ray norm in $(0,\,12\|A\|(d+1)TL|B|]$. Here $1≤H$, $0≤L$, $0<h$, $0<Y≤T$, $Th^2=H$, $YH≤T$, and $B$ is the nonempty second set of the configuration. All new losses depend only on the fixed chart and dimension once $A$ has been chosen.
