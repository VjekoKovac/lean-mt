# AI proof and clarity review of Proposition 3.1

Two AI agents compared the Lean proof with §3 of the six authors’ arXiv v1. One agent reviewed the other contributors’ chart phase, cap areas, physical change of variables, line estimates, assembly of Proposition 3.1 and the final projection in §4.4. A second agent, who did not write the numerator proof, reviewed its affine normalization and packet integrals. No human author review is recorded here. [Source, §3](https://arxiv.org/html/2611.22465v1#S3) · [Source, §4](https://arxiv.org/html/2611.22465v1#S4)

## Mathematical checks

| Question in the paper | Finding from the proof bodies |
| --- | --- |
| Which constants may depend on the configuration? | The chart, signed curvature coefficient, area factor, chart radius, and positive small constant $c$ are fixed before $H,L,A,B$. The transfer proof works for every real $H\ge1$ and $L\ge1$. The output uses $H^{1+2/\beta}$, one factor of $L$, and both cardinalities. |
| Must every principal direction have curvature? | A reflection puts one nonisotropic vector in the distinguished coordinate. The norm of the full Hessian controls the mixed and transverse terms on each cube. This gives the necessary phase bound for either sign of the nonzero coefficient. |
| Which affine map acts on frequencies? | The invertible linear part $F$ reverses the rigid chart, rotates the horizontal space, subtracts the tangent linear form, and divides the last coordinate by $q=D^2\phi(u)[Ee_j,Ee_j]/2\ne0$. Its affine translation subtracts $F(g(u))$. Subtracting the two frequencies of a packet pair cancels this translation. |
| Which map acts on physical space? | In the Fourier pairing $\langle F\xi,y\rangle=\langle\xi,F^*y\rangle$, set $A=F^*$. The new integral contains $\mathcal E f(Ay)$. In the original variables take $w'(x)=w(A^{-1}x)$, so the numerator is multiplied by $\lvert\det A\rvert$. This follows from the Haar change of variables, including orientation-reversing maps. |
| Are the surface patches actually on the original surface? | Cube images lie inside one fixed chart neighborhood contained in the surface. Their surface measure is the specified Euclidean-normalized Hausdorff area. Projection onto the base gives a lower bound $(2\varepsilon)^d$ and a local Lipschitz upper bound gives $K^d(2\varepsilon)^d$. |
| Does the numerator use finite measures legitimately? | The Bochner integral is on each measurable patch of finite mass. The phase has modulus one and the input has constant amplitude there. The packet expansion uses finite sums and products of these measures. The Fourier kernel is nonnegative everywhere and at least the product of the individual quarter-scale lower bounds on resonant pairs. The ordered multiplicity is exactly the energy. |
| Which powers of $\varepsilon$ survive? | The squared amplitude contributes $\varepsilon^{-d}$, each of two areas contributes $(2\varepsilon)^d$, and the kernel contributes $(Y/4)^d(T/4)$. Their product is $(Y\varepsilon)^dT/4$. The widths satisfy $Y\varepsilon=c$, leaving a positive factor fixed before $H$. Disjointness is used for the squared input norm. |
| Does the line estimate survive changing coordinates? | Every original unit line with direction $v$ is sent by $A^{-1}$ to a line of speed $\lVert A^{-1}v\rVert$. Its reciprocal is at most $\lVert A\rVert$. The estimate holds for every offset, including nonperpendicular offsets after the map. The support radius also gains a factor $\lVert A\rVert$. Continuity, $w'(0)=|B|^2>0$ and positive sphere area give a strictly positive X-ray norm. |
| Is the tested quotient valid? | The integrable cap input has positive finite squared norm, and the constructed continuous weight has positive finite X-ray norm. The actual pair is inserted into the supremum only after both estimates. Its gain is bounded below by the positive chart constant $c_E/(c_Fc_X)$ times $E(A,B)/(L|A||B|)$. |

These checks explain two differences from the paper’s presentation. The Lean argument uses constant indicators on surface patches, so two-sided patch area bounds suffice in place of explicitly computing the graph Jacobian of the parameterization. It also bounds the transverse quadratic terms by an operator norm after choosing one curved direction. The paper gives a full diagonal local normal form. No claim of a separate formal proof of that normal-form lemma in its stated generality is needed here.

## One-file review of the arithmetic projection

An AI reviewer independent of the arithmetic implementation read `MT/FieldProjection.lean` against the gaps and strip argument of §4.4. The algebraic input assumes integrality and an absolute bound $M\ge1$ at every real place. A coordinate difference is bounded by $2M$ at all places. A doubled area is the difference of two products of coordinate differences and is bounded by $8M^2$. The proof applies the norm gap before the horizontal and vertical divisions by $M$ and $M^2$. A determinant is divided by $M^3$. The common scale $H=(100M^3\cdot8M^2)^{[K:\mathbb Q]}$ therefore works for all three gaps. A strip of vertical width $H^{-1}$ contains only collinear lifts, with vertical pairs handled separately by the ordinate gap. Injectivity and compatibility of the parabolic projection with addition preserve both cardinalities and the ordered energy. The field-set construction, its covolume estimates and its field tower are inputs to this file. Its check covers the projection once those inputs have been supplied.

## Repeating the checks

Run the commands below from the repository root. The short `example` in the second command restates Proposition 3.1 independently of the names `AnalyticTransfer` and `Configuration.gain`. It makes the dependence of the constants, the radius, and the denominator visible. The six following commands in the file print transitive axioms for the individual stages. Reading the source and studying its correspondence with the arXiv theorem still requires mathematical judgment.

```bash
lake build MT.AnalyticTransfer MT.FieldProjection
lake env lean checks/AnalyticReview.lean
```

[Replay input](../checks/AnalyticReview.lean) · [Recorded output](../checks/analytic-review.txt)
