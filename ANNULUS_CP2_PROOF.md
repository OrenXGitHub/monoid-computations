# Proof for the 122-element model of `CP^2`

This note proves that the monoid `M_122` constructed by
`annulus_cp2.py` satisfies

```text
B M_122 ~= CP^2.
```

The proof does not infer a homotopy type from finite-range cohomology.
The companion program `verify_annulus_cp2.py` checks, with exact finite
arithmetic, every explicit category, simplicial, monoid, and cocycle identity
used below. The remaining implications are standard results about classifying
spaces of categories, homotopy colimits, and oriented circle bundles.

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

The last equivalence is the standard rectangular-band model of `S^2`; it is
also proved in the accompanying paper.

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

Their realizations are an annulus and a circle. Define simplicial maps on the
universal covers by

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

We use the following special case of the framed-collage construction.

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

The collage lemma identifies `B G^-` with the homotopy pushout

```text
* <- B El(P) -> B K,
```

hence with the asserted homotopy cofiber.

Complete `G^-` to a category `G` by adjoining

```text
G(d,*) = K(d,d_0),
G(d,d') = K(d,d') disjoint-union (P(d') x K(d,d_0)).
```

Composition is induced by composition in `K`, the functor `P`, and the
unique element of `P(d_0)`. The mixed associativity identities reduce to
functoriality of `P` and uniqueness of that element. We claim that the
inclusion `G^- -> G` is a homotopy equivalence.

For the object `*`, the comma category `(G^- downarrow *)` deformation
retracts onto the arrow from `*` to `d_0` determined by the unique element of
`P(d_0)`; the resulting subcategory has a terminal object. For an object
`d_1` of `K`, `(G^- downarrow d_1)` deformation retracts onto the full
subcategory containing the arrows `p:* -> d_1`, the identity of `d_1`, and,
for every `p in P(d_1)`, the corresponding added arrow `d_0 -> d_1`. The
subcategory on the first two kinds of objects has terminal object
`id_(d_1)`, and the comma category below each added object has terminal
object given by the framed arrow `* -> d_0`. Quillen's Theorem A, first for
these inclusions and then for `G^- -> G`, proves `B G^- ~= B G`.

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
`[omega] in H^2(BD;Z)`. This is the standard description of a principal
simplicial `B Z`-bundle by a normalized integral 2-cocycle.

We next identify (2) with the map in (1). Let `P_tilde` be the diagram over
`D_omega x Delta_{<=2}^op` with values `A_tilde_q` and `C_tilde_q`, where
`(delta,n)` acts as `tau^n delta_tilde`. Quotienting by deck transformations
defines

```text
El(P_tilde) -> El(P).
```

This functor is an equivalence. It is surjective on objects. Given two lifted
objects and an arrow between their images, there is a unique deck translation
of the chosen lifted arrow carrying the first simplex to the second. Thus it
is also fully faithful.

The projection

```text
El(P_tilde) -> D_omega
```

is the Grothendieck construction of the truncated simplex categories of
`A_tilde` and `C_tilde`. Their classifying spaces are respectively
`|A_tilde|` and `|C_tilde|`: truncation at degree two loses nothing because
these simplicial sets have no nondegenerate simplices above dimensions two
and one. Both spaces are contractible. Thomason's homotopy-colimit theorem
(equivalently, Quillen's Theorem B applied to this Grothendieck opfibration)
therefore shows that

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
`B L0 ~= S^2`. Hence both `H_2(BD;Z)` and `H^2(BD;Z)` are infinite cyclic.
Equation (3) forces both `[z]` and `[omega]` to be generators, up to sign.

Principal oriented circle bundles over `S^2` are classified by their Euler
class. The bundle with Euler class `+1` or `-1` has total space `S^3` and is,
up to orientation, the Hopf fibration. Consequently

```text
B El(P) -> B K  ~=  S^3 -> S^2
```

with the map on the right a Hopf map.

Combining this with (1) gives

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

- D. Quillen, *Higher algebraic K-theory I*, Lecture Notes in Mathematics
  341 (1973), especially Theorem A.
- R. W. Thomason, *Homotopy colimits in the category of small categories*,
  Math. Proc. Cambridge Philos. Soc. 85 (1979), 91-109.
- J. P. May, *Simplicial Objects in Algebraic Topology*, Chapters 18-19, for
  twisted cartesian products and realization of simplicial principal bundles.
