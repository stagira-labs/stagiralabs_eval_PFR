import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.GroupTheory.Complement
import PFR.ForMathlib.MeasureReal.Indep
import PFR.EntropyPFR
import PFR.Tactic.RPowSimp
import VerifiedAgora.tagger
/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-!
# Polynomial Freiman-Ruzsa conjecture

Here we prove the polynomial Freiman-Ruzsa conjecture.
-/

open ProbabilityTheory MeasureTheory Real Set Fintype Function
open scoped Pointwise

universe u

namespace ProbabilityTheory
variable {G Ω : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Finset G}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V` with probability `#(A ∩ B) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub_zero (Uunif : IsUniform A U) (Umeas : Measurable U)
    (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {0})
      = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
  have : (U - V) ⁻¹' {0} = ⋃ (g : G), (U ⁻¹' {g} ∩ V⁻¹' {g}) := by
    ext ω; simp [sub_eq_zero, eq_comm]
  rw [this, measureReal_iUnion_fintype _
    (fun i ↦ (Umeas .of_discrete).inter $ Vmeas .of_discrete)]; swap
  · intro g g' hgg'
    apply Set.disjoint_iff_inter_eq_empty.2
    ext a
    simp (config := {contextual := True}) [hgg']
  classical
  let W : Finset G := A ∩ B
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [h_indep.measureReal_inter_preimage_eq_mul .of_discrete .of_discrete]
    _ = ∑ p ∈ W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_subset W.subset_univ _).symm
        intro i _ hi
        replace hi : i ∉ A ∨ i ∉ B := by simp [W] at hi; tauto
        rcases hi with h'i|h'i
        · simp [Uunif.measureReal_preimage_of_nmem h'i]
        · simp [Vunif.measureReal_preimage_of_nmem h'i]
    _ = ∑ p ∈ W, (1 / Nat.card A : ℝ) * (1 / Nat.card B) := by
        apply Finset.sum_congr rfl (fun i hi ↦ ?_)
        replace hi : i ∈ A ∧ i ∈ B := by simpa [W] using hi
        rw [Uunif.measureReal_preimage_of_mem (by trivial) hi.1,
            Vunif.measureReal_preimage_of_mem (by trivial) hi.2]
    _ = (W.card : ℝ) / (Nat.card A * Nat.card B) := by simp [div_eq_inv_mul]; ring
    _ = Nat.card (A ∩ B : Set G) / (Nat.card A * Nat.card B) := by
        congr
        rw [← Finset.coe_inter, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
        simp

/-- Given two independent random variables `U` and `V` uniformly distributed respectively on `A`
and `B`, then `U = V + x` with probability `# (A ∩ (B + x)) / #A ⬝ #B`. -/
lemma IsUniform.measureReal_preimage_sub (Uunif : IsUniform A U) (Umeas : Measurable U)
    (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V) (x : G) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {x})
      = Nat.card (A ∩ (B + {x}) : Set G) / (Nat.card A * Nat.card B) := by
  classical
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x} : Set G) W := by
    convert Vunif.comp (add_left_injective x)
    simp
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_add_const x
    exact h_indep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp only [W, mem_preimage, Pi.add_apply, mem_singleton_iff, Pi.sub_apply, ← sub_eq_zero (b := x)]
    abel_nf
  have h : (B : Set G)+{x} = (B+{x}:Finset G) := by simp
  rw [h] at Wunif
  rw [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]
  congr 3
  · rw [add_singleton]; simp
  convert Finset.card_vadd_finset (AddOpposite.op x) B
  · simp
  simp

end ProbabilityTheory


/-- Record positivity results that are useful in the proof of PFR. -/
@[target]
lemma PFR_conjecture_pos_aux {G : Type*} [AddCommGroup G] {A : Set G} [Finite A] {K : ℝ}
    (h₀A : A.Nonempty) (hA : Nat.card (A - A) ≤ K * Nat.card A) :
    (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A - A) ∧ 0 < K := by sorry

@[target]
lemma PFR_conjecture_pos_aux' {G : Type*} [AddCommGroup G] {A : Set G} [Finite A] {K : ℝ}
    (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := by sorry


variable {G : Type*} [AddCommGroup G] {A : Set G} {K : ℝ} [Countable G]

/-- A uniform distribution on a set with doubling constant `K` has self Rusza distance
at most `log K`. -/
@[target]
theorem rdist_le_of_isUniform_of_card_add_le [A_fin : Finite A] [MeasurableSpace G]
    [MeasurableSingletonClass G]
    (h₀A : A.Nonempty) (hA : Nat.card (A - A) ≤ K * Nat.card A)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # U₀] ≤ log K := by sorry

variable [Module (ZMod 2) G] [Fintype G]
@[target]
lemma sumset_eq_sub {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] (A : Set G) :
    A + A = A - A := by sorry
/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if `A` is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup `H`
such that `A` can be covered by at most `K^(13/2) |A|^(1/2) / |H|^(1/2)` cosets of `H`, and `H` has
the same cardinality as `A` up to a multiplicative factor `K^11`. -/
@[target]
lemma PFR_conjecture_aux (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ (13/2 : ℝ) * Nat.card A ^ (1/2 : ℝ) * Nat.card H ^ (-1/2 : ℝ)
      ∧ Nat.card H ≤ K ^ 11 * Nat.card A ∧ Nat.card A ≤ K ^ 11 * Nat.card H ∧ A ⊆ c + H := by sorry

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if `A` is a subset of an elementary abelian
2-group of doubling constant at most `K`, then `A` can be covered by at most `2 * K ^ 12` cosets of
a subgroup of cardinality at most `|A|`. -/
@[target]
theorem PFR_conjecture (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by sorry


/-- Corollary of `PFR_conjecture` in which the ambient group is not required to be finite (but) then
`H` and `c` are finite. -/
@[target]
theorem PFR_conjecture' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by sorry
