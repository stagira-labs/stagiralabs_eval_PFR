import PFR.ForMathlib.CompactProb
import PFR.ForMathlib.Entropy.RuzsaDist
import VerifiedAgora.tagger
/-!
# The tau functional

Definition of the tau functional and basic facts

## Main definitions:

* `η`: $1/9$
* `τ`: The tau functional $\tau[X_1; X_2] = d[X_1; X_2] + \eta d[X^0_1; X_1] + \eta d[X^0_2; X_2].$

## Main results

* `tau_minimizer_exists`: A pair of random variables minimizing $\tau$ exists.
* `condRuzsaDistance_ge_of_min`: If $X_1,X_2$ is a tau-minimizer with $k = d[X_1;X_2]$, then $d[X'_1|Z, X'_2|W]$ is at least
$$k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] )$$
for any $X'_1, Z, X'_2, W$.
-/

open MeasureTheory ProbabilityTheory
universe uG

variable (Ω₀₁ Ω₀₂ : Type*) [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
  variable (G : Type uG) [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- A structure that packages all the fixed information in the main argument. In this way, when
defining the τ functional, we will only only need to refer to the package once in the notation
instead of stating the reference spaces, the reference measures and the reference random
variables.

The η parameter has now been incorporated into the package, in preparation for being able to
manipulate the package. -/
structure refPackage where
  /-- The first variable in a package. -/
  X₀₁ : Ω₀₁ → G
  /-- The second variable in a package. -/
  X₀₂ : Ω₀₂ → G
  hmeas1 : Measurable X₀₁
  hmeas2 : Measurable X₀₂
  /-- The constant that parameterizes how good the package is. The argument only works for
  small enough `η`, typically `≤ 1/9` or `< 1/8`. -/
  η : ℝ
  hη : 0 < η
  hη' : 8 * η ≤ 1

variable (p : refPackage Ω₀₁ Ω₀₂ G)
variable {Ω₀₁ Ω₀₂ G}

variable {Ω Ω' Ω₁ Ω₂ Ω'₁ Ω'₂ S T : Type*}

/-- If $X_1,X_2$ are two $G$-valued random variables, then
$$ \tau[X_1; X_2] := d[X_1; X_2] + \eta d[X^0_1; X_1] + \eta d[X^0_2; X_2].$$
Here, $X^0_1$ and $X^0_2$ are two random variables fixed once and for all in most of the argument.
To lighten notation, We package `X^0_1` and `X^0_2` in a single object named `p`.

We denote it as `τ[X₁ ; μ₁ # X₂ ; μ₂ | p]` where `p` is a fixed package containing the information
of the reference random variables. When the measurable spaces have a canonical measure `ℙ`, we
can use `τ[X₁ # X₂ | p]`
-/
noncomputable def tau {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (X₁ : Ω₁ → G) (X₂ : Ω₂ → G) (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) : ℝ :=
  d[X₁ ; μ₁ # X₂ ; μ₂] + p.η * d[p.X₀₁ ; ℙ # X₁ ; μ₁] + p.η * d[p.X₀₂ ; ℙ # X₂ ; μ₂]

@[inherit_doc tau]
notation3:max "τ[" X₁ " ; " μ₁ " # " X₂ " ; " μ₂ " | " p"]" => tau p X₁ X₂ μ₁ μ₂

@[inherit_doc tau]
notation3:max "τ[" X₁ " # " X₂ " | " p"]" => tau p X₁ X₂ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume
@[target]
lemma continuous_tau_restrict_probabilityMeasure
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ τ[id ; μ.1 # id ; μ.2 | p]) := by sorry

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[Fintype G] in
/-- If $X'_1, X'_2$ are copies of $X_1,X_2$, then $\tau[X'_1;X'_2] = \tau[X_1;X_2]$. -/
@[target]
lemma ProbabilityTheory.IdentDistrib.tau_eq [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Ω'₁] [MeasurableSpace Ω'₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ'₁ : Measure Ω'₁} {μ'₂ : Measure Ω'₂}
    {X₁ : Ω₁ → G} {X₂ : Ω₂ → G} {X₁' : Ω'₁ → G} {X₂' : Ω'₂ → G}
    (h₁ : IdentDistrib X₁ X₁' μ₁ μ'₁) (h₂ : IdentDistrib X₂ X₂' μ₂ μ'₂) :
    τ[X₁ ; μ₁ # X₂ ; μ₂ | p] = τ[X₁' ; μ'₁ # X₂' ; μ'₂ | p] := by sorry

/-- Property recording the fact that two random variables minimize the tau functional. Expressed
in terms of measures on the group to avoid quantifying over all spaces, but this implies comparison
with any pair of random variables, see Lemma `is_tau_min`. -/
def tau_minimizes {Ω : Type*} [MeasureSpace Ω] (X₁ : Ω → G) (X₂ : Ω → G) : Prop :=
  ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[X₁ # X₂ | p] ≤ τ[id ; ν₁ # id ; ν₂ | p]

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[Fintype G] in
/-- If $X'_1, X'_2$ are copies of $X_1,X_2$, then $X_1, X_2$ minimize $\tau$ iff $X_1', X_2'$ do. -/
@[target]
lemma ProbabilityTheory.IdentDistrib.tau_minimizes [MeasureSpace Ω]
    [MeasureSpace Ω']
    {X₁ X₂ : Ω → G} {X₁' X₂' : Ω' → G}
    (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂') :
    tau_minimizes p X₁ X₂ ↔ tau_minimizes p X₁' X₂' := by sorry

/-- A pair of measures minimizing $\tau$ exists. -/
@[target]
lemma tau_min_exists_measure [MeasurableSingletonClass G] :
    ∃ (μ : Measure G × Measure G),
    IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 ∧
    ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[id ; μ.1 # id ; μ.2 | p] ≤ τ[id ; ν₁ # id ; ν₂ | p] := by sorry

/-- A pair of random variables minimizing $τ$ exists. -/
@[target]
lemma tau_minimizer_exists [MeasurableSingletonClass G] :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
    Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω) ∧
    tau_minimizes p X₁ X₂ := by sorry

variable [MeasureSpace Ω] [hΩ₁ : MeasureSpace Ω'₁] [hΩ₂ : MeasureSpace Ω'₂]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω'₁)] [IsProbabilityMeasure (ℙ : Measure Ω'₂)]
  {X₁ : Ω → G} {X₂ : Ω → G} {X₁' : Ω'₁ → G} {X₂' : Ω'₂ → G}

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Fintype G]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
@[target]
lemma is_tau_min (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂') :
    τ[X₁ # X₂ | p] ≤ τ[X₁' # X₂' | p] := by sorry



omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Fintype G]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Let `X₁` and `X₂` be tau-minimizers associated to `p`, with $d[X_1,X_2]=k$, then
$$ d[X'_1;X'_2] \geq
    k - \eta (d[X^0_1;X'_1] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2] - d[X^0_2;X_2] )$$
for any $G$-valued random variables $X'_1,X'_2$.
-/
@[target]
lemma distance_ge_of_min (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂') :
    d[X₁ # X₂] - p.η * (d[p.X₀₁ # X₁'] - d[p.X₀₁ # X₁]) - p.η * (d[p.X₀₂ # X₂'] - d[p.X₀₂ # X₂])
      ≤ d[X₁' # X₂'] := by sorry

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Fintype G]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Version of `distance_ge_of_min` with the measures made explicit. -/
@[target]
lemma distance_ge_of_min' {Ω'₁ Ω'₂ : Type*} (h : tau_minimizes p X₁ X₂)
    [MeasurableSpace Ω'₁] [MeasurableSpace Ω'₂] {μ : Measure Ω'₁} {μ' : Measure Ω'₂}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {X₁': Ω'₁ → G} {X₂': Ω'₂ → G}
    (h1 : Measurable X₁') (h2 : Measurable X₂') :
    d[X₁ # X₂] - p.η * (d[p.X₀₁; ℙ # X₁'; μ] - d[p.X₀₁ # X₁])
      - p.η * (d[p.X₀₂; ℙ # X₂'; μ'] - d[p.X₀₂ # X₂]) ≤ d[X₁'; μ # X₂'; μ'] := by
  set M1 : MeasureSpace Ω'₁ := { volume := μ }
  set M2 : MeasureSpace Ω'₂ := { volume := μ' }
  exact distance_ge_of_min p h h1 h2

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For any $G$-valued random variables $X'_1,X'_2$ and random variables $Z,W$, one can lower
bound $d[X'_1|Z;X'_2|W]$ by
$$k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] ).$$
-/
@[target]
lemma condRuzsaDistance_ge_of_min [MeasurableSingletonClass G]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂')
    (Z : Ω'₁ → S) (W : Ω'₂ → T) (hZ : Measurable Z) (hW : Measurable W) :
    d[X₁ # X₂] - p.η * (d[p.X₀₁ # X₁' | Z] - d[p.X₀₁ # X₁])
      - p.η * (d[p.X₀₂ # X₂' | W] - d[p.X₀₂ # X₂]) ≤ d[X₁' | Z # X₂' | W] := by sorry
