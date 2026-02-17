import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Constructions.SubmoduleQuotient
import PFR.Mathlib.Data.Set.Pointwise.SMul
import PFR.Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import PFR.ForMathlib.AffineSpaceDim
import PFR.ForMathlib.Entropy.RuzsaSetDist
import PFR.ImprovedPFR
import VerifiedAgora.tagger
/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int`: Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$.
  There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-17}\lvert A\rvert$ and
  $\dim A' \leq (40/\log 2)\log K$.

-/

open Set
open scoped Pointwise
section AddCommGroup
variable {G : Type*} [AddCommGroup G] {A B : Set G}

/-- A set `A` is a shift of a set `B` if it can be written as `x + B`. -/
def IsShift (A B : Set G) : Prop := ∃ x : G, A = x +ᵥ B
@[target]
lemma IsShift.sub_self_congr : IsShift A B → A - A = B - B := by sorry

@[target]
lemma IsShift.card_congr : IsShift A B → Nat.card A = Nat.card B := by sorry

/-- The property of two sets A, B of a group G not being contained in cosets of the same proper
subgroup -/
def NotInCoset (A B : Set G) : Prop := AddSubgroup.closure ((A - A) ∪ (B - B)) = ⊤

/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of
non-empty sets into a subgroup where they are not in a coset. -/
@[target]
lemma wlog_notInCoset (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (G' : AddSubgroup G) (A' B' : Set (G' : Set G)),
    IsShift A A' ∧ IsShift B B' ∧ NotInCoset A' B' := by sorry


end AddCommGroup

section Torsion

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [Countable G] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G)
  (μ : Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If `G` is torsion-free and `X, Y` are `G`-valued random variables then `d[X ; 2Y] ≤ 5d[X ; Y]`. -/
@[target]
lemma torsion_free_doubling [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (hG : AddMonoid.IsTorsionFree G) :
    d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X ; μ # Y ; μ'] := by sorry



/-- If `G` is a torsion-free group and `X, Y` are `G`-valued random variables and
`φ : G → 𝔽₂^d` is a homomorphism then `H[φ ∘ X ; μ] ≤ 10 * d[X ; μ # Y ; μ']`. -/
@[target]
lemma torsion_dist_shrinking {H : Type*} [FiniteRange X] [FiniteRange Y] (hX : Measurable X)
    (hY : Measurable Y) [AddCommGroup H] [Module (ZMod 2) H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
    H[φ ∘ X ; μ] ≤ 10 * d[X ; μ # Y ; μ'] := by sorry

end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [MeasurableSpace G]
[MeasurableSingletonClass G] {Ω Ω' : Type*}

/-- Let $G=\mathbb{F}_2^n$ and `X, Y` be `G`-valued random variables such that
\[\mathbb{H}(X)+\mathbb{H}(Y)> (20/\alpha) d[X ;Y],\]
for some $\alpha > 0$.
There is a non-trivial subgroup $H\leq G$ such that
\[\log \lvert H\rvert <(1+\alpha)/2 (\mathbb{H}(X)+\mathbb{H}(Y))\] and
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))< \alpha (\mathbb{H}(X)+\mathbb{H}(Y))\]
where $\psi:G\to G/H$ is the natural projection homomorphism.
-/
@[target]
lemma app_ent_PFR' [mΩ : MeasureSpace Ω] [mΩ' : MeasureSpace Ω'] (X : Ω → G) (Y : Ω' → G)
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    {α : ℝ} (hent : 20 * d[X # Y] < α * (H[X] + H[Y])) (hX : Measurable X) (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) < (1 + α) / 2 * (H[X] + H[Y]) ∧
      H[H.mkQ ∘ X] + H[H.mkQ ∘ Y] < α * (H[X] + H[Y]) := by sorry

variable [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G)
(μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac)
[IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

@[target]
lemma app_ent_PFR (α : ℝ) (hent : 20 * d[X ;μ # Y;μ'] < α * (H[X ; μ] + H[Y; μ'])) (hX : Measurable X)
    (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) < (1 + α) / 2 * (H[X ; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X ; μ] + H[H.mkQ ∘ Y; μ'] < α * (H[ X ; μ] + H[Y; μ']) := by sorry

set_option maxHeartbeats 300000 in
/-- If $G=\mathbb{F}_2^d$ and `X, Y` are `G`-valued random variables and $\alpha < 1$ then there is
a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq (1 + α) / (2 * (1 - α)) * (\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 20/\alpha * d[\psi(X);\psi(Y)].\] -/
@[target]
lemma PFR_projection'
    (α : ℝ) (hX : Measurable X) (hY : Measurable Y) (αpos : 0 < α) (αone : α < 1) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) ≤ (1 + α) / (2 * (1 - α)) * (H[X ; μ] + H[Y ; μ']) ∧
    α * (H[H.mkQ ∘ X ; μ] + H[H.mkQ ∘ Y ; μ']) ≤
      20 * d[H.mkQ ∘ X ; μ # H.mkQ ∘ Y ; μ'] := by sorry

/-- If $G=\mathbb{F}_2^d$ and `X, Y` are `G`-valued random variables then there is
a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2 * (\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 34 * d[\psi(X);\psi(Y)].\] -/
@[target]
lemma PFR_projection (hX : Measurable X) (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) ≤ 2 * (H[X ; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X ; μ] + H[H.mkQ ∘ Y; μ'] ≤
      34 * d[H.mkQ ∘ X ;μ # H.mkQ ∘ Y;μ'] := by sorry

end F2_projection

open MeasureTheory ProbabilityTheory Real Set
@[target]
lemma four_logs {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    log ((a*b)/(c*d)) = log a + log b - log c - log d := by sorry

@[target]
lemma sum_prob_preimage {G H : Type*} {X : Finset H} {A : Set G} [Finite A] {φ : A → X}
    {A_ : H → Set G} (hA : A.Nonempty) (hφ : ∀ x : X, A_ x = Subtype.val '' (φ ⁻¹' {x})) :
    ∑ x ∈ X, (Nat.card (A_ x) : ℝ) / Nat.card A = 1 := by sorry

/-- Let $\phi : G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets.
If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$.
There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}
\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
@[target]
lemma single_fibres {G H Ω Ω': Type*}
    [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup H] [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    (φ : G →+ H)
    {A B : Set G} [Finite A] [Finite B] {UA : Ω → G} {UB : Ω' → G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hUA': Measurable UA) (hUB': Measurable UB) (hUA : IsUniform A UA) (hUB : IsUniform B UB)
    (hUA_mem : ∀ ω, UA ω ∈ A) (hUB_mem : ∀ ω, UB ω ∈ B) :
    ∃ (x y : H) (Ax By : Set G),
    Ax = A ∩ φ.toFun ⁻¹' {x} ∧ By = B ∩ φ.toFun ⁻¹' {y} ∧ Ax.Nonempty ∧ By.Nonempty ∧
    d[φ.toFun ∘ UA # φ.toFun ∘ UB]
    * log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By))) ≤
    (H[φ.toFun ∘ UA] + H[φ.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by sorry

variable {G : Type*} [AddCommGroup G] [Module.Free ℤ G]

open Real MeasureTheory ProbabilityTheory Pointwise Set Function
open QuotientAddGroup

variable [Module.Finite ℤ G]


/-- A version of the third isomorphism theorem: if G₂ ≤ G and H' is a subgroup of G⧸G₂, then there
is a canonical isomorphism between H⧸H' and G⧸N, where N is the preimage of H' in G. A bit clunky;
may be a better way to do this -/
@[target]
lemma third_iso {G : Type*} [AddCommGroup G] {G₂ : AddSubgroup G} (H' : AddSubgroup (G ⧸ G₂)) :
    let H := G ⧸ G₂
    let φ : G →+ H := mk' G₂
    let N := AddSubgroup.comap φ H'
    ∃ e : H ⧸ H' ≃+ G ⧸ N, ∀ x : G, e (mk' H' (φ x)) = mk' N x := by sorry



variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N
and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty,
one has the inequality $$\log\frac{|A| |B|}{|A_x| |B_y|} ≤ 34 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound $$n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B]$$.
 -/
@[target]
lemma weak_PFR_asymm_prelim (A B : Set G) [A_fin : Finite A] [B_fin : Finite B]
    (hnA : A.Nonempty) (hnB : B.Nonempty):
    ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G), Ax.Nonempty ∧ By.Nonempty ∧
    Set.Finite Ax ∧ Set.Finite By ∧ Ax = {z : G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧
    By = {z : G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧
    (log 2) * Module.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) +
      40 * dᵤ[ A # B ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By)
      ≤ 34 * (dᵤ[ A # B ] - dᵤ[ Ax # By ]) := by sorry


/-- Separating out the conclusion of `weak_PFR_asymm` for convenience of induction arguments.-/
def WeakPFRAsymmConclusion (A B : Set G) : Prop :=
  ∃ A' B' : Set G, A' ⊆ A ∧ B' ⊆ B ∧ A'.Nonempty ∧ B'.Nonempty ∧
  log ((Nat.card A * Nat.card B) / (Nat.card A' * (Nat.card B'))) ≤ 34 * dᵤ[A # B] ∧
  max (AffineSpace.finrank ℤ A') (AffineSpace.finrank ℤ B') ≤ (40 / log 2) * dᵤ[A # B]

/-- The property of two sets A,B of a group G not being contained in cosets of the same proper subgroup -/
def not_in_coset {G : Type*} [AddCommGroup G] (A B : Set G) : Prop :=
  AddSubgroup.closure ((A - A) ∪ (B - B)) = ⊤

/-- In fact one has equality here, but this is trickier to prove and not needed for the argument. -/
@[target]
lemma dimension_of_shift {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (A : Set H) (x : G) :
    AffineSpace.finrank ℤ ((fun a : H ↦ (a : G) + x) '' A) = AffineSpace.finrank ℤ A := by sorry

omit [Module.Finite ℤ G] [Module.Free ℤ G] in
@[target]
lemma conclusion_transfers {A B : Set G}
    (G': AddSubgroup G) (A' B' : Set (G' : Set G))
    (hA : IsShift A A') (hB : IsShift B B') [Finite A'] [Finite B']
    (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (h : WeakPFRAsymmConclusion A' B') : WeakPFRAsymmConclusion A B := by sorry

/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty
$A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 34 d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
@[target]
lemma weak_PFR_asymm (A B : Set G) [Finite A] [Finite B] (hA : A.Nonempty) (hB : B.Nonempty) :
    WeakPFRAsymmConclusion A B := by sorry

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then
there exists a non-empty $A'\subseteq A$ such that $\lvert A'\rvert\geq K^{-17}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
@[target]
lemma weak_PFR {A : Set G} [Finite A] {K : ℝ} (hA : A.Nonempty) (hK : 0 < K)
    (hdist : dᵤ[A # A] ≤ log K) :
    ∃ A' : Set G, A' ⊆ A ∧ K^(-17 : ℝ) * Nat.card A ≤ Nat.card A' ∧
      AffineSpace.finrank ℤ A' ≤ (40 / log 2) * log K := by sorry

/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$.
There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-17}\lvert A\rvert$
and $\dim A' \leq \frac{40}{\log 2} \log K$.-/
@[target]
theorem weak_PFR_int
    {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} [A_fin : Finite A] (hnA : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A-A) ≤ K * Nat.card A) :
    ∃ A' : Set G, A' ⊆ A ∧ Nat.card A' ≥ K ^ (-17 : ℝ) * Nat.card A ∧
      AffineSpace.finrank ℤ A' ≤ (40 / log 2) * log K := by sorry
