# Proof for the 122-element model of `CP^2`

This note proves that the monoid `M_122` constructed by
`annulus_cp2.py` satisfies

```text
B M_122 ~= CP^2.
```

The proof does not infer a homotopy type from finite-range cohomology and does
not use the accompanying article. It is self-contained apart from the
published results cited below. The companion program `verify_annulus_cp2.py`
checks, with exact finite arithmetic, every explicit category, simplicial,
monoid, and cocycle identity used in the argument.

## 1. The category and the simplicial diagram

Let `L0` be the five-element monoid

```text
L0 = {1} union {x_kj : k,j in {0,1}},
x_kj x_k'j' = x_kj'.
```

Let `D` be the category with two objects `a,b` and

```text
D(a,a) = L0,       D(b,b) = {1},
D(a,b) = {r_0,r_1},  D(b,a) = {i_0,i_1},
r_j i_k = 1_b,       i_k r_j = x_kj.
```

Thus `b` is a retract of `a`. The retract-generator lemma (an immediate
application of Quillen's Theorem A) gives

```text
B D ~= B L0 ~= S^2.
```

The last equivalence is Fiedorowicz's five-element rectangular-band model of
`S^2` [Fie02].

Let `A_tilde` be the simplicial set whose `q`-simplices are nondecreasing
integer sequences

```text
n_0 <= ... <= n_q <= n_0 + 2,
```

and let `C_tilde` be defined similarly with width one. Translation by two on
`A_tilde` and by one on `C_tilde` gives quotient simplicial sets

```text
A = A_tilde/(n ~ n+2),       C = C_tilde/(n ~ n+1).
```

The nondegenerate simplices of `C_tilde` form a triangulated line, while those
of `A_tilde` form the strip of triangles with vertices
`{n,n+1,n+2}`. Thus both universal covers are contractible, and the two
quotients are respectively a circle and an annulus. Define simplicial maps on
the universal covers by

```text
i_k(c) = 2c+k,               r_j(n) = floor((n+j)/2).
```

They descend to maps `i_k:C -> A` and `r_j:A -> C`. Entrywise application
defines the action of `D`, with `x_kj=i_k r_j`.

Put

```text
K = D x Delta_{<=2}^op,
P(a,[q]) = A_q,              P(b,[q]) = C_q.
```

Then `P:K -> Set` is a finite functor. It is framed at

```text
d_0 = (b,[0]),
```

because `P(d_0)=C_0` is a singleton. Every object of `K` is a retract of

```text
c_0 = (a,[2]).
```

The program checks functoriality for every arrow of `D`, every simplicial
operator between dimensions zero, one, and two, the frame, and all required
retracts. It also finds

```text
|A_0|,|A_1|,|A_2| = 2,6,12,
|C_0|,|C_1|,|C_2| = 1,2,3.
```

## 2. The framed-collage lemma

We first record the two standard categorical facts used here. If every object
of a category `K` is a retract of `c_0`, the inclusion

```text
End_K(c_0) -> K
```

is a homotopy equivalence. Indeed, Quillen's Theorem A reduces this to the
comma categories of arrows `c_0 -> d`; the one for `d=c_0` has terminal object
`id_(c_0)`, and a chosen retraction of `d` from `c_0` exhibits the general one
as a retract of it.

We also use the following special case of the collage construction. For a
functor `P:K -> Set`, form the category with one extra object `*`, arrows
`* -> d` given by `P(d)`, no arrows `d -> *`, and the original arrows within
`K`. Its classifying space is the homotopy pushout

```text
* <- B El(P) -> B K.                                  (C)
```

This is the two-sided Grothendieck construction for the displayed span, so
(C) follows directly from Thomason's homotopy-colimit theorem. Equivalently,
inserting the objects of `El(P)` produces the usual double mapping cylinder.

We now use the following special framed version of these facts.

**Lemma.** Let `K` be a finite category, let `P:K -> Set` be finite, and
suppose that `P(d_0)` is a singleton. If every object of `K` is a retract of
`c_0`, there is a finite monoid

```text
M = K(c_0,c_0) disjoint-union
    (P(c_0) x K(c_0,d_0))
```

whose products, besides composition in `K(c_0,c_0)`, are

```text
(p,alpha)(p',alpha') = (p,alpha'),
delta (p,alpha)       = (P(delta)(p),alpha),
(p,alpha) delta       = (p,alpha delta).
```

This monoid satisfies

```text
B M ~= Cof(B El(P) -> B K).
```

Here `El(P)` is the category of elements and the displayed map is its
projection to `K`.

**Proof.** Introduce a new object `*`. First form the collage `G^-` with

```text
G^-(*,*) = {1},       G^-(*,d) = P(d),
G^-(d,d') = K(d,d'),  G^-(d,*) = empty.
```

The collage comparison (C) identifies `B G^-` with the homotopy pushout

```text
* <- B El(P) -> B K,
```

hence with the asserted homotopy cofiber.

Let `s_0:* -> d_0` be the arrow determined by the unique element of
`P(d_0)`. Adjoin an arrow `rho:d_0 -> *` subject to
`rho s_0=id_*`. Reduction by this relation gives the unique normal forms

```text
G(d,*) = K(d,d_0),
G(d,d') = K(d,d') disjoint-union (P(d') x K(d,d_0)),
```

where `(p,alpha)` represents `p rho alpha`. Composition is induced by
composition in `K` and functoriality of `P`; associativity is automatic from
the presentation by the generator `rho` and the single relation.

Let `J:G^- -> G` be the inclusion. The comma category `(J downarrow *)` has
terminal object `(d_0,rho)`: the unique morphism to it is `s_0` from
`(*,id_*)` and is `alpha` from an object `(d,rho alpha)`.

For `d_1` in `K`, `(J downarrow d_1)` retracts onto the full subcategory `R`
whose objects are

```text
(*,p),               p in P(d_1),
(d_1,id_(d_1)),
(d_0,p rho),         p in P(d_1).
```

The retraction sends an old arrow `beta:d -> d_1` to `(d_1,id_(d_1))` and an
added arrow `p rho alpha:d -> d_1` to `(d_0,p rho)`; the components are
respectively `beta` and `alpha`. Let `T` be the full subcategory on the first
two displayed kinds of objects. It has terminal object `(d_1,id_(d_1))`, and
for each remaining object `(d_0,p rho)`, the comma category
`(T downarrow (d_0,p rho))` has the single object represented by
`s_0:(*,p) -> (d_0,p rho)`. Quillen's Theorem A gives `B T ~= B R`, so `R`
and hence `(J downarrow d_1)` are contractible. Applying the theorem once more
to `J` proves `B G^- ~= B G`.

The framed arrows make `*` a retract of `d_0`. Since every object of `K` is a
retract of `c_0`, every object of `G` is a retract of `c_0`. A second use of
the retract-generator lemma gives

```text
B End_G(c_0) ~= B G ~= B G^-.
```

Finally, direct inspection of `End_G(c_0)` gives the displayed set `M` and
its multiplication. This proves the lemma.

For the annulus diagram, the lemma gives

```text
M = (L0 x O_3^op) disjoint-union
    (A_2 x {r_0,r_1} x {0,1,2}).
```

It has `5*10 + 12*2*3 = 122` elements. The verification program constructs
this endomorphism multiplication from the framed data and compares every one
of its `122^2` products with the table in `annulus_cp2.py`. They agree.
Therefore that table is the monoid in the framed-collage lemma, and

```text
B M_122 ~= Cof(B El(P) -> B K).                 (1)
```

## 3. The map is the Hopf fibration

Choose the lifts on vertices

```text
i_k_tilde(c) = 2c+k,
r_j_tilde(n) = floor((n+j)/2),
x_kj_tilde = i_k_tilde r_j_tilde.
```

If `tau` denotes the relevant deck transformation, then for composable
arrows `delta,delta'` of `D` there is an integer `omega(delta,delta')` such
that

```text
delta_tilde delta'_tilde
    = tau^omega(delta,delta') (delta delta')_tilde.
```

The program derives `omega` from these lifts, rather than assuming it. It
checks the normalized cocycle identity on every composable triple. Explicitly,

```text
omega(delta,delta') = 1
```

exactly when

```text
delta  in {r_1,x_01,x_11}
delta' in {i_1,x_10,x_11},
```

and it is zero otherwise.

Let `D_omega` have the same objects as `D`, with arrows `(delta,n)` for
`n in Z` and composition

```text
(delta,n)(delta',n')
  = (delta delta', n+n'+omega(delta,delta')).
```

The projection

```text
B D_omega -> B D                                      (2)
```

is the principal `B Z = S^1`-bundle classified by
`[omega] in H^2(BD;Z)`. More explicitly, its nerve is the twisted cartesian
product `N(D) x_omega N(Z)`: over a composable `q`-tuple in `D`, a simplex is
a `q`-tuple of integers, and the twisted face is precisely the displayed
composition law. The standard realization theorem for twisted cartesian
products therefore gives the asserted principal circle bundle.

We next identify (2) with the map in (1). Let `P_tilde` be the diagram over
`D_omega x Delta_{<=2}^op` with values `A_tilde_q` and `C_tilde_q`, where
`(delta,n)` acts as `tau^n delta_tilde`. Quotienting by deck transformations
defines

```text
El(P_tilde) -> El(P).
```

This functor is an equivalence. It is surjective on objects. For fixed lifts
of its source and target, an arrow in `El(P)` has a unique integer deck shift
making the lifted simplex identity hold; this gives a unique arrow in
`El(P_tilde)`. Thus the functor is fully faithful.

The projection

```text
El(P_tilde) -> D_omega
```

is the projection from the Grothendieck construction of the truncated simplex
categories of `A_tilde` and `C_tilde`. Their classifying spaces are
respectively `|A_tilde|` and `|C_tilde|`: truncation at degree two loses
nothing because these simplicial sets have no nondegenerate simplices above
dimensions two and one. Both spaces are contractible. Thomason's
homotopy-colimit theorem therefore shows that

```text
B El(P_tilde) ~= B D_omega.
```

The construction commutes with the projections to `D`. Since
`B Delta_{<=2}^op` is contractible, it follows that the map

```text
B El(P) -> B K
```

is equivalent, as an arrow over `BD`, to `B D_omega -> B D`.

It remains to identify its Euler class. Inside `D(a,a)=L0`, put

```text
z = -(x_11,x_11) -(x_00,x_00)
    +(x_10,x_10) +(x_11,x_00).
```

With the normalized bar boundary

```text
d(alpha,beta) = alpha - alpha beta + beta,
```

one has `d z=0`. The program checks this identity and obtains

```text
<omega,z> = -1.                                      (3)
```

The inclusion `L0=D(a,a) -> D` is a homotopy equivalence, and
`B L0 ~= S^2`. Hence both `H_2(BD;Z)` and `H^2(BD;Z)` are infinite cyclic,
and the universal coefficient theorem identifies their evaluation pairing
with multiplication in `Z`. Equation (3) therefore forces both `[z]` and
`[omega]` to be generators, up to sign.

Principal oriented circle bundles over `S^2` are classified by their Euler
class. The bundle with Euler class `+1` or `-1` has total space `S^3` and is,
up to orientation, the Hopf fibration. Consequently

```text
B El(P) -> B K  ~=  S^3 -> S^2
```

with the map on the right a Hopf map.

Combining this with (1) and the standard CW decomposition
`CP^2 = S^2 union_eta e^4` gives

```text
B M_122 ~= Cof(S^3 -> S^2) ~= CP^2.
```

This proves the claim.

## 4. Reproducing the finite checks

Install the dependencies listed in `requirements.txt`, then run

```bash
python verify_annulus_cp2.py
```

The final line should be

```text
All finite hypotheses in ANNULUS_CP2_PROOF.md passed.
```

The cohomology calculations in `annulus_cp2.py` are useful independent
checks, but they are not used in the proof above.

## References for the quoted results

- [Fie02] Z. Fiedorowicz, *A counterexample to a group completion conjecture of
  J. C. Moore*, Algebr. Geom. Topol. 2 (2002), 33-35,
  https://doi.org/10.2140/agt.2002.2.33.
- D. Quillen, *Higher algebraic K-theory I*, Lecture Notes in Mathematics
  341 (1973), especially Theorem A.
- R. W. Thomason, *Homotopy colimits in the category of small categories*,
  Math. Proc. Cambridge Philos. Soc. 85 (1979), 91-109.
- J. P. May, *Simplicial Objects in Algebraic Topology*, Chapters 18-19, for
  twisted cartesian products and realization of simplicial principal bundles.
