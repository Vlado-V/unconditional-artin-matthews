module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantTwoSidedExpandedRootTransfer
public import ArtinMatthews.GiantTwoSidedPhysicalPairing
public import ArtinMatthews.GiantCandidatePhysicalPairingBudget
public import ArtinMatthews.GiantTwoSidedEndpointBudget
public import ArtinMatthews.MarkedPhysicalEndpointNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal candidate endpoints, with their extra half-damping,
fit the original physical pairing on a dyad. Bounded position factors
include the Mellin phases and the normalized reciprocal position. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

theorem giantCandidatePhysicalEndpointPairing_eventually_of_moment {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (χ : DirichletCharacter ℂ m) {γ τ q : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (j k ell : ℕ) (hj : 0 < j) (Cstep E : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      let P := fun g : ↥groups => giantCandidateGroup x g.val
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      ∀ (I : Type u) (patterns : Finset I) (C : I → ↥groups → Finset (Fin k))
        (step : ℤ), (step.natAbs : ℝ) ≤ L^Cstep →
      ∀ (ζ : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (X : ℝ),
        x^τ ≤ X → X ≤ x^(1/τ) →
      let roots := giantTwoSidedRootInterval X
      let Z := giantTwoSidedRootSlice X
      let T := giantTwoSidedExpandedPhysicalMoment (fun _ : Fin n => patterns) (fun _ => C)
        (fun i => if i.val%2 = 0 then step else -step) q (fun i => if i.val%2 = 0 then ζ else -ζ)
        (fun i p a b aux => if i.val%2 = 0 then K p a b aux else star (K p b a aux)) roots Z
      ‖T‖ / ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) ≤ (L^(-E))^n →
      ∀ (u v : ℕ → ℂ), (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
      let F (r : ℕ) := if r ∈ roots then u r * conj (giantCandidateFirstEndpoint e ε x r) else 0
      let G (r : ℕ) := v r * (χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
        (Finset.univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r)
      let d (r : ℕ) := (giantTwoSidedEndpointDamping P (k+ell) q r : ℂ)
      ‖giantTwoSidedPhysicalWeightedPairing (giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C step q ζ K)
        (fun s => d s.val.1.val * F s.val.1.val) (fun s => d s.val.1.val * G s.val.1.val)‖ ≤
          8*X*L^(-E+((j*j:ℕ):ℝ)+2) := by
  let B : ℝ := ((j*j:ℕ):ℝ)/2+1
  have hB : 0 ≤ B := by unfold B; positivity
  filter_upwards [giantCandidatePhysicalPairing_eventually_of_moment.{u} k ell Cstep B E q hB hτ,
    giantCandidateTwoSidedEndpointNorm_budget_eventually e he hε hεq χ hγ hτ
      (R := 4) (by norm_num) hq j hj, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hpair hnorm hx hL
  intro groups P L n I patterns C step hstep ζ K X hX hXhi roots Z T hT u v hu hv F G d
  let F₀ (r : ℕ) := conj (giantCandidateFirstEndpoint e ε x r)
  let G₀ (r : ℕ) := χ r*giantCandidateAllocationCore (giantCandidateFullPrimes x) (Finset.univ.biUnion P)
    (Real.exp (L^(6/25 : ℝ))) (x^γ) j r
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let σ := markedPhysicalMass (fun g => bandReciprocalMass (P g)) (k+ell)
  let f (r : ℕ) := d r*F r
  let g (s : State) := d s.val.1.val*G s.val.1.val
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hX1 : 1 ≤ X := (Real.one_le_rpow hx.le hτ.le).trans hX
  have hZ : Z ⊆ Finset.Ioc 0 ⌊4*X⌋₊ := by
    intro r hr
    obtain ⟨hr0,hr1⟩ := Finset.mem_Ioc.mp hr
    have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 3*X)).le
    exact Finset.mem_Ioc.mpr ⟨hr0, hr1.trans (Nat.le_floor (by linarith))⟩
  obtain ⟨hSup,hNF,hNG⟩ := hnorm groups (k+ell) X hX1 hXhi Z hZ
  have hf0 (r : ℕ) (hr : r ∉ roots) : f r = 0 := by simp only [f,F,hr,ite_false,mul_zero]
  have hfSup (r : ℕ) (hr : r ∈ roots) : ‖f r‖ ≤ Real.exp (Real.sqrt L) := by
    change ‖d r * (if r ∈ roots then u r * F₀ r else 0)‖ ≤ _
    rw [ite_eq_left hr, mul_left_comm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hu r hr)).trans (hSup r)
  have hFmono : ∀ r ∈ Z, ‖F r‖ ≤ ‖F₀ r‖ := by
    intro r _
    change ‖if r ∈ roots then u r * F₀ r else 0‖ ≤ _
    split_ifs with hr
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hu r hr)
    · simp only [norm_zero,norm_nonneg]
  have hF' := (giantTwoSidedEndpointNorm_mono P (k+ell) Z q hFmono).trans hNF
  have hG' := (giantTwoSidedEndpointNorm_mul_le P (k+ell) Z q v G₀ hv).trans hNG
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ =>
    Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have henergy (w : State → ℂ) (hw : Real.sqrt (∑ s : State, σ*‖w s‖^2) ≤ Real.sqrt X*L^B) :
      (∑ s : State, σ*‖w s‖^2) ≤ X*L^(2*B) := by
    have hz : 0 ≤ ∑ s : State, σ*‖w s‖^2 := Finset.sum_nonneg (fun _ _ => mul_nonneg hσ (sq_nonneg _))
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hw 2
    rw [Real.sq_sqrt hz, mul_pow, Real.sq_sqrt (zero_le_one.trans hX1),
      ← Real.rpow_mul_natCast hL0.le] at hh
    simpa only [Nat.cast_ofNat, mul_comm B (2:ℝ)] using hh
  have hF := henergy (fun s => f s.val.1.val) hF'
  have hG := henergy g hG'
  have h := hpair groups I patterns C step hstep ζ K X hX hT f g hf0 hfSup hF hG
  have hexp : -E+2*B = -E+((j*j:ℕ):ℝ)+2 := by unfold B; ring
  simpa only [hexp] using h

end
end ArtinMatthews
