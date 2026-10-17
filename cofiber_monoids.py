#!/usr/bin/env python3
"""
cofiber_monoids.py -- finite monoids whose classifying spaces are mapping cones.

CONSTRUCTION.  Let L be a finite monoid, Y a finite REDUCED simplicial set of dimension <= n and
g : Y -> N(L) a simplicial map (equivalently a homomorphism from the fundamental monoid of Y to L).
Write O = End_Delta([n]) (order-preserving self-maps of {0..n}) and  Y~_n = Y_n x L  (the pull-back of
the universal L-set).  Put

        M(Y,g)  =  O^op   |_|   ( Y_n x L x {0..n} ),

where the second piece is an ideal:
        (y,l,i) (y',l',i')  =  ( y,  l * hol_i(y') * l',  i' ),      hol_i(y') = product of the edge labels of y' after vertex i
        theta . (y,l,i)     =  ( theta^* y,  hol_{theta(n)}(y) * l,  i )
        (y,l,i) . theta     =  ( y, l, theta(i) ).

CLAIM (Theorem A of the accompanying notes):   B M(Y,g)  ~  Cof( |Y| --|g|--> BL ).

In this file Y is given as a simplicial subset of the nerve N(H) of an auxiliary monoid H (finite or
infinite) together with a homomorphism phi : H -> L; then g = N(phi) restricted to Y.

The script builds several such monoids, checks associativity, and computes H^*(BM; F_2) as a ring
(Ext over F_2[M] with Yoneda products), using a projective resolution built from Dold-Kan idempotents.
The main example is a 1795-element monoid with BM ~ CP^2.

Requires only the Python standard library (numpy is used for the associativity check if present).
"""
import itertools, sys, time
from fractions import Fraction
from collections import Counter

# ----------------------------------------------------------------------------------------------
# 1.  order-preserving maps and Dold-Kan idempotents
# ----------------------------------------------------------------------------------------------
def mono_maps(n):
    return [t for t in itertools.product(range(n + 1), repeat=n + 1) if all(t[i] <= t[i + 1] for i in range(n))]
def comp(f, g): return tuple(f[x] for x in g)                              # f o g
def face(k, i): return tuple(y if y < i else y + 1 for y in range(k))      # delta^i : [k-1] -> [k]
def degen(k, j): return tuple(x if x <= j else x - 1 for x in range(k + 1))  # sigma^j : [k] -> [k-1]
def _add(a, b):
    c = Counter(a); c.update(b); return frozenset(t for t, v in c.items() if v % 2)
def _opmul(A, B):     # theta stands for the operator X(theta);  X(t1) X(t2) = X(t2 o t1)
    c = Counter(comp(t2, t1) for t1 in A for t2 in B); return frozenset(t for t, v in c.items() if v % 2)
def _normalizer(k):
    """projector of X_k onto N_k = ker d_1 n ... n ker d_k along the degenerate part, as an element of F_2[End([k])]"""
    one = frozenset([tuple(range(k + 1))])
    if k == 0: return one
    thetas = [comp(face(k, j + 1), degen(k, j)) for j in range(k)]         # s_j d_{j+1}
    for order in itertools.permutations(range(k)):
        P = one
        for j in order: P = _opmul(P, _add(one, frozenset([thetas[j]])))
        if (_opmul(P, P) == P and all(not _opmul(frozenset([face(k, i)]), P) for i in range(1, k + 1))
                and all(not _opmul(P, frozenset([degen(k, j)])) for j in range(k))):
            return P
    raise RuntimeError("normalizer not found")
def dk_idempotents(n):
    """orthogonal idempotents eps_0..eps_n of F_2[End([n])^op]; eps_k projects X_n onto sigma_k^* N_k(X)."""
    out = []
    for k in range(n + 1):
        dlt = tuple(range(k + 1)); sg = tuple(min(x, k) for x in range(n + 1))
        out.append(frozenset(comp(comp(dlt, phi), sg) for phi in _normalizer(k)))
    return out

# ----------------------------------------------------------------------------------------------
# 2.  the monoid M(Y,g)
# ----------------------------------------------------------------------------------------------
def cofiber_monoid(mulH, oneH, phi, L, gens, n):
    """gens: n-tuples of elements of H generating Y_n (the simplicial subset of N(H) they generate, padded with oneH).
    Returns (multiplication table with identity at index 0, element labels, list of n-simplices of Y)."""
    O = mono_maps(n)
    def op(theta, s):
        out = []
        for j in range(1, n + 1):
            r = oneH
            for x in s[theta[j - 1]:theta[j]]: r = mulH(r, x)
            out.append(r)
        return tuple(out)
    S = set(tuple(g) for g in gens) | {(oneH,) * n}; todo = list(S)
    while todo:
        s = todo.pop()
        for th in O:
            t = op(th, s)
            if t not in S: S.add(t); todo.append(t)
    S = sorted(S, key=repr); nL = len(L)
    def hol(s, i):
        r = 0
        for x in s[i:]: r = L[r][phi(x)]
        return r
    els = [('o', tuple(range(n + 1)))] + [('o', th) for th in O if th != tuple(range(n + 1))]
    els += [('k', s, l, i) for s in S for l in range(nL) for i in range(n + 1)]
    idx = {e: k for k, e in enumerate(els)}
    def mult(x, y):
        if x[0] == 'o' and y[0] == 'o': return ('o', tuple(y[1][x[1][j]] for j in range(n + 1)))   # product in O^op
        if x[0] == 'o':
            th = x[1]; _, s, l, i = y; return ('k', op(th, s), L[hol(s, th[n])][l], i)
        if y[0] == 'o':
            _, s, l, i = x; return ('k', s, l, y[1][i])
        _, s, l, i = x; _, s2, l2, i2 = y
        return ('k', s, L[L[l][hol(s2, i)]][l2], i2)
    mul = [[idx[mult(a, b)] for b in els] for a in els]
    return mul, els, S

def is_monoid(mul):
    n = len(mul)
    if any(mul[0][a] != a or mul[a][0] != a for a in range(n)): return False
    try:
        import numpy as np
        A = np.array(mul, dtype=np.int32)
        return all(np.array_equal(A[A[a]], A[a][A]) for a in range(n))
    except ImportError:
        return all(mul[mul[a][b]][c] == mul[a][mul[b][c]] for a in range(n) for b in range(n) for c in range(n))

# ----------------------------------------------------------------------------------------------
# 3.  H^*(BM; F_2) as a ring.  Vectors of (F_2 M)^r are Python ints (bit j*|M|+a).
# ----------------------------------------------------------------------------------------------
def popcount(x): return bin(x).count("1")
class Span:
    def __init__(self): self.piv = {}
    def reduce(self, v):
        while v:
            p = self.piv.get(v.bit_length() - 1)
            if p is None: return v
            v ^= p
        return 0
    def add(self, v):
        v = self.reduce(v)
        if v: self.piv[v.bit_length() - 1] = v; return True
        return False
    def dim(self): return len(self.piv)
class TagSpan:
    def __init__(self): self.piv = {}
    def reduce(self, v, tag=0):
        while v:
            p = self.piv.get(v.bit_length() - 1)
            if p is None: return v, tag
            v ^= p[0]; tag ^= p[1]
        return 0, tag
    def add(self, v, tag):
        v, tag = self.reduce(v, tag)
        if v: self.piv[v.bit_length() - 1] = (v, tag); return None
        return tag
def nullspace_bits(rows, ncols):
    TS = TagSpan(); out = []
    for c in range(ncols):
        v = 0
        for i, r in enumerate(rows):
            if (r >> c) & 1: v |= 1 << i
        rel = TS.add(v, 1 << c)
        if rel is not None: out.append(rel)
    return out

class Resolution:
    """projective resolution of the trivial F_2[M]-module by sums of A.eps, eps in a full family of idempotents of A=F_2[M]"""
    def __init__(self, mul, types):
        self.mul = mul; self.n = n = len(mul)
        self.eps = list(types); self.aug = [popcount(e) & 1 for e in types]
        assert self.aug[0] == 1 and all(self.amul(e, e) == e for e in types)
        self.basis = []
        for e in types:
            S = Span(); B = []
            for m in range(n):
                v = self.lmul(m, e)
                if S.add(v): B.append(v)
            self.basis.append(B)
        self.order = sorted(range(len(types)), key=lambda c: len(self.basis[c]))
        self.gens = [[(0, None)]]; self.solver = []; self.ker = []; self.top = 0
        self._elim(0)
    def lmul(self, x, v):
        n = self.n; row = self.mul[x]; out = 0
        while v:
            low = v & -v; b = low.bit_length() - 1; v ^= low
            j, a = divmod(b, n); out ^= 1 << (j * n + row[a])
        return out
    def amul(self, a, v):
        out = 0
        while a:
            low = a & -a; out ^= self.lmul(low.bit_length() - 1, v); a ^= low
        return out
    def _elim(self, k):
        n = self.n; TS = TagSpan(); rels = []
        for j, (c, w) in enumerate(self.gens[k]):
            for beta in self.basis[c]:
                r = TS.add(self.amul(beta, w) if k >= 1 else (popcount(beta) & 1), beta << (j * n))
                if r is not None: rels.append(r)
        self.solver.append(TS); self.ker.append(rels)
    def extend(self):
        k = self.top; K = self.ker[k]; target = len(K); S = Span(); gens = []
        for c in self.order:
            if S.dim() >= target: break
            for v in K:
                w = self.amul(self.eps[c], v)
                if w and S.reduce(w):
                    gens.append((c, w))
                    for beta in self.basis[c]: S.add(self.amul(beta, w))
                    if S.dim() >= target: break
        assert S.dim() == target, "the family of idempotents is not full"
        keep = list(range(len(gens)))
        for i in reversed(range(len(gens))):
            T = Span()
            for j in keep:
                if j != i:
                    for beta in self.basis[gens[j][0]]: T.add(self.amul(beta, gens[j][1]))
            if T.dim() == target: keep.remove(i)
        self.gens.append([gens[i] for i in keep]); self.top = k + 1; self._elim(k + 1)
    def augrow(self, k, j):
        n = self.n; w = self.gens[k][j][1]; out = 0; mask = (1 << n) - 1
        for i in range(len(self.gens[k - 1])):
            if popcount((w >> (i * n)) & mask) & 1: out |= 1 << i
        return out
    def allowed(self, k):
        return sum(1 << j for j, (c, _) in enumerate(self.gens[k]) if self.aug[c])
    def cohomology(self, k):
        rk = len(self.gens[k]); al = self.allowed(k)
        rows = [self.augrow(k + 1, j) & al for j in range(len(self.gens[k + 1]))]
        rows += [1 << j for j in range(rk) if not (al >> j) & 1]
        Z = nullspace_bits(rows, rk); Bd = Span()
        if k >= 1:
            A = [self.augrow(k, j) for j in range(rk)]; alp = self.allowed(k - 1)
            for i in range(len(self.gens[k - 1])):
                if (alp >> i) & 1: Bd.add(sum(1 << j for j in range(rk) if (A[j] >> i) & 1) & al)
        S = Span()
        for p in Bd.piv.values(): S.add(p)
        return [z for z in Z if S.add(z)], Bd
    def product(self, psi, m, phi, a):
        """Yoneda product of psi in H^m and phi in H^a, as a cochain on P_{a+m}"""
        n = self.n; mask = (1 << n) - 1
        F = [self.amul(self.eps[c], self.eps[0]) if (phi >> j) & 1 else 0 for j, (c, _) in enumerate(self.gens[a])]
        for i in range(1, m + 1):
            G = []
            for (c, w) in self.gens[a + i]:
                t = 0; v = w
                while v:
                    low = v & -v; b = low.bit_length() - 1; v ^= low
                    j, x = divmod(b, n); t ^= self.lmul(x, F[j])
                r, tag = self.solver[i].reduce(t, 0); assert r == 0
                G.append(self.amul(self.eps[c], tag))
            F = G
        out = 0
        for g in range(len(self.gens[a + m])):
            if sum(1 for i in range(len(self.gens[m])) if (psi >> i) & 1 and popcount((F[g] >> (i * n)) & mask) & 1) & 1:
                out |= 1 << g
        return out

def ring(name, mul, els, n, maxdeg=5, verbose=True):
    idx = {e: k for k, e in enumerate(els)}; N = len(mul)
    dk = [sum(1 << idx[('o', th)] for th in eps) for eps in dk_idempotents(n)]
    small = [1 << a for a in range(N) if els[a][0] == 'k' and mul[a][a] == a]
    small.sort(key=lambda e: len(set(mul[x][e.bit_length() - 1] for x in range(N))))
    R = Resolution(mul, small[:1] + dk)
    for k in range(maxdeg + 1): R.extend()
    H = {k: R.cohomology(k)[0] for k in range(maxdeg + 1)}
    betti = [len(H[k]) for k in range(maxdeg + 1)]
    prods = {}
    for a in range(1, maxdeg + 1):
        for b in range(a, maxdeg + 1 - a):
            if H[a] and H[b]:
                nz = any(R.cohomology(a + b)[1].reduce(R.product(psi, b, phi, a) & R.allowed(a + b)) for phi in H[a] for psi in H[b])
                prods[(a, b)] = nz
    if verbose:
        print(f"{name}\n    |M| = {N};  F_2 Betti numbers b_0..b_{maxdeg} = {betti}")
        for (a, b), nz in prods.items(): print(f"    H^{a} x H^{b} -> H^{a+b}: {'NONZERO' if nz else 'zero'}")
        sys.stdout.flush()
    return betti, prods

# ----------------------------------------------------------------------------------------------
# 4.  examples
# ----------------------------------------------------------------------------------------------
def table_monoid(T): return (lambda a, b: T[a][b]), 0
C2 = [[0, 1], [1, 0]]
# L0 = Fiedorowicz's monoid: identity 0 and x_ij = 1+2i+j with x_ij x_kl = x_il ;  B L0 = S^2
L0 = [[0] * 5 for _ in range(5)]
for a in range(5): L0[0][a] = a; L0[a][0] = a
for i, j, k, l in itertools.product(range(2), repeat=4): L0[1 + 2 * i + j][1 + 2 * k + l] = 1 + 2 * i + l
def u(a, b):
    """a normalized 2-cocycle generating H^2(L0; Z) = Z :  u(x_ij, x_kl) = [j = 0][k = 0]"""
    return 1 if (a and b and (a - 1) % 2 == 0 and (b - 1) // 2 == 0) else 0
# P = L0 x_u Z, the central extension of L0 by Z with class u:  B P = S^3 and  B(P -> L0) is the Hopf map
def mulP(p, q): return (L0[p[0]][q[0]], p[1] + q[1] + u(p[0], q[0]))
ONE = (0, 0)
HOPF_SPHERE = [  # 12 tetrahedra of N(P); together with their faces: 1 vertex, 7 edges, 18 triangles, 12 tetrahedra
    ((2, -1), (0, 1), (2, -1)), ((2, -1), (0, 1), (3, -1)), ((2, -1), (2, 0), (2, 0)), ((2, 0), (2, 0), (2, -1)),
    ((2, 0), (3, 0), (3, -1)), ((1, -1), (0, 1), (2, -1)), ((1, -1), (0, 1), (3, -1)), ((1, -1), (2, 0), (3, -1)),
    ((1, 0), (2, -1), (3, 0)), ((1, 0), (1, -1), (1, -1)), ((1, 0), (1, -1), (3, 0)), ((1, 0), (3, 0), (3, -1))]

def faces(s, mul_, one):
    k = len(s); out = [s[1:]]
    for i in range(1, k): out.append(s[:i - 1] + (mul_(s[i - 1], s[i]),) + s[i + 1:])
    out.append(s[:-1]); return [f for f in out]
def solve_rat(rows, rhs):
    m = len(rows); n = len(rows[0]); A = [[Fraction(v) for v in r] + [Fraction(b)] for r, b in zip(rows, rhs)]
    piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; inv = 1 / A[r][c]; A[r] = [v * inv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
        if r == m: break
    assert all(A[i][n] == 0 for i in range(r, m)), "inconsistent"
    x = [Fraction(0)] * n
    for i, c in enumerate(piv): x[c] = A[i][n]
    return x, piv

def det_bareiss(A):
    """Exact determinant of a square integer matrix."""
    A = [row[:] for row in A]; n = len(A)
    if n == 0: return 1
    sign = 1; previous = 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if A[i][k]), None)
        if pivot_row is None: return 0
        if pivot_row != k:
            A[k], A[pivot_row] = A[pivot_row], A[k]; sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * pivot - A[i][k] * A[k][j]) // previous
        previous = pivot
        for i in range(k + 1, n): A[i][k] = 0
    return sign * A[-1][-1]

def hopf_sphere_check():
    """Exact check: Y is simply connected, has integral homology S^3, and is oriented to have Hopf invariant 1."""
    K = [1, 2, 3, 4]; mulL = lambda a, b: L0[a][b]
    S3 = list(itertools.product(K, repeat=3)); S4 = list(itertools.product(K, repeat=4)); i3 = {s: i for i, s in enumerate(S3)}
    assert all(u(b, c) - u(L0[a][b], c) + u(a, L0[b][c]) - u(a, b) == 0 for a, b, c in S3), "u is not a cocycle"
    # w with dw = u cup u on N(L0)
    rows = [[0] * len(S3) for _ in S4]
    for r, s in enumerate(S4):
        for i, f in enumerate(faces(s, mulL, 0)): rows[r][i3[f]] += (-1) ** i
    w, _ = solve_rat(rows, [u(s[0], s[1]) * u(s[2], s[3]) for s in S4])
    assert all(x.denominator == 1 for x in w)
    C = HOPF_SPHERE; T = sorted({f for s in C for f in faces(s, mulP, ONE)}); E = sorted({f for t in T for f in faces(t, mulP, ONE)})
    jt = {s: i for i, s in enumerate(T)}; je = {s: i for i, s in enumerate(E)}
    D3 = [[0] * len(C) for _ in T]; D2 = [[0] * len(T) for _ in E]
    for j, s in enumerate(C):
        for i, f in enumerate(faces(s, mulP, ONE)): D3[jt[f]][j] += (-1) ** i
    for j, s in enumerate(T):
        for i, f in enumerate(faces(s, mulP, ONE)): D2[je[f]][j] += (-1) ** i

    # Exact integral certificate.  The first unit minor makes D2 surjective.  The second makes
    # im(D3) primitive of rank 11.  Since D2 D3 = 0 and ker(D2) also has rank 11, im(D3)=ker(D2).
    d2cols = (0, 1, 2, 3, 5, 11, 12)
    d3rows = (0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 13)
    d3cols = tuple(range(1, 12))
    assert det_bareiss([[D2[i][j] for j in d2cols] for i in range(7)]) == -1
    assert det_bareiss([[D3[i][j] for j in d3cols] for i in d3rows]) == -1
    assert all(sum(D2[i][k] * D3[k][j] for k in range(len(T))) == 0
               for i in range(len(E)) for j in range(len(C)))

    # The triangle relation (a,b) is [a][b]=[ab].  Repeated cancellation in these relations
    # proves that all seven edge generators are trivial in the fundamental group.
    rels = [(je[(s[0],)], je[(s[1],)], je[(mulP(s[0], s[1]),)]) for s in T]
    trivial = set()
    changed = True
    while changed:
        changed = False
        for a, b, c in rels:
            forced = set()
            if a == c or (a in trivial and c in trivial): forced.add(b)
            if b == c or (b in trivial and c in trivial): forced.add(a)
            if a in trivial and b in trivial: forced.add(c)
            old = len(trivial); trivial.update(forced); changed |= len(trivial) != old
    assert trivial == set(range(len(E)))

    def rank_mod(Mx, p):
        Mx = [[v % p for v in r] for r in Mx]; r = 0
        for c in range(len(Mx[0])):
            pr = next((i for i in range(r, len(Mx)) if Mx[i][c]), None)
            if pr is None: continue
            Mx[r], Mx[pr] = Mx[pr], Mx[r]; inv = pow(Mx[r][c], -1, p); Mx[r] = [v * inv % p for v in Mx[r]]
            for i in range(len(Mx)):
                if i != r and Mx[i][c]: f = Mx[i][c]; Mx[i] = [(a - f * b) % p for a, b in zip(Mx[i], Mx[r])]
            r += 1
        return r
    for p in (2, 3, 5, 7, 32749):
        assert rank_mod(D2, p) == len(E) and rank_mod(D3, p) == len(T) - len(E) == len(C) - 1
    # fundamental cycle (kernel of D3 is one-dimensional)
    _, piv = solve_rat(D3, [0] * len(T)); free = [c for c in range(len(C)) if c not in piv][0]
    z, _ = solve_rat(D3 + [[1 if c == free else 0 for c in range(len(C))]], [0] * len(T) + [1])
    assert all(v.denominator == 1 for v in z)
    hopf = sum(z[j] * (-s[0][1] * u(s[1][0], s[2][0]) - (w[i3[(s[0][0], s[1][0], s[2][0])]] if 0 not in (s[0][0], s[1][0], s[2][0]) else 0))
               for j, s in enumerate(C))
    if hopf == -1:
        z = [-v for v in z]
        hopf = -hopf
    assert hopf == 1
    print(f"Hopf sphere Y: 1 vertex, {len(E)} edges, {len(T)} triangles, {len(C)} tetrahedra; pi_1 = 0;"
          f" H_1 = H_2 = 0, H_3 = Z (certified by unit integer minors);"
          f" fundamental cycle has coefficients +-1: {all(abs(v) == 1 for v in z)}; Hopf invariant of |Y| -> BL0 = {hopf}")
    return hopf

if __name__ == "__main__":
    t0 = time.time()
    mH, oH = table_monoid(C2)
    print("=== sanity checks of the claim  BM(Y,g) ~ Cof(|Y| -> BL) ===")
    for name, n, L, phi, expect in (
            ("Sigma RP^2          [Y = sk_2 N(C2), L = 1]     expect Betti 1,0,1,1,0 and all products zero", 2, [[0]], (lambda h: 0), None),
            ("Sigma RP^3          [Y = sk_3 N(C2), L = 1]     expect Betti 1,0,1,1,1,0 and all products zero", 3, [[0]], (lambda h: 0), None),
            ("RP^inf / RP^1       [Y = sk_1 N(C2), L = C2]    expect Betti 1,0,1,1,1,1 and the ring of the ideal (w^2) in F_2[w]", 1, C2, (lambda h: h), None),
            ("RP^inf / RP^2       [Y = sk_2 N(C2), L = C2]    expect Betti 1,0,0,1,1,1", 2, C2, (lambda h: h), None)):
        mul, els, S = cofiber_monoid(mH, oH, phi, L, list(itertools.product(range(2), repeat=n)), n)
        assert is_monoid(mul); ring(name, mul, els, n, 5)
    mL, oL = table_monoid(L0)
    mul, els, S = cofiber_monoid(mL, oL, (lambda h: h), L0, [(1, 1), (4, 4), (2, 2), (1, 4)], 2)
    assert is_monoid(mul); ring("cone off the generator of pi_2(B L0) = pi_2(S^2)      expect Betti 1,0,0,0,0,0 (contractible)", mul, els, 2, 5)
    f = (1, -1)
    mul, els, S = cofiber_monoid(mulP, ONE, (lambda h: h[0]), L0, [(f, f, f)], 3)
    assert is_monoid(mul); ring("control: a null-homotopic 3-sphere in N(P) -> N(L0)     expect S^2 v S^4: Betti 1,0,1,0,1,0 and x^2 = 0", mul, els, 3, 5)
    print("\n=== the main example: CP^2 ===")
    h = hopf_sphere_check()
    mul, els, S = cofiber_monoid(mulP, ONE, (lambda h: h[0]), L0, HOPF_SPHERE, 3)
    print(f"M = M(Y_Hopf -> L0): {len(S)} three-simplices in Y, |M| = {len(mul)};  associative and unital: {is_monoid(mul)}")
    betti, prods = ring("H^*(BM; F_2)      expect Betti 1,0,1,0,1,0,0,0,0,0 and x^2 != 0, i.e. F_2[x]/(x^3)", mul, els, 3, 9)
    ok = betti == [1, 0, 1, 0, 1, 0, 0, 0, 0, 0] and prods.get((2, 2)) and h == 1
    print("\nRESULT:", "the mod-2 cohomology ring is F_2[x]/(x^3) through degree 9 and the Hopf invariant is 1  ==>  BM ~ CP^2" if ok else "UNEXPECTED")
    print(f"(total time {time.time() - t0:.0f}s)")
