module

public import ArtinMatthews.MarkedMinorArcPositionOperator
public import ArtinMatthews.MarkedMinorArcEndpoints
public import ArtinMatthews.MarkedMinorArcProductAtoms
public import ArtinMatthews.MarkedMinorArcWeightedConjugation
public import ArtinMatthews.MarkedMinorArcProductEndpoints
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual PD prime-product measure in the clean position block. The true
baseline tilt, growing moment length and band normalizers are retained. -/
namespace ArtinMatthews
open Matrix MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator

/-- Zero extension of the actual pushed positive prime-product measure. -/
noncomputable def markedMinorIntegerProductMass {J : Type*} [Fintype J]
    (e : J → ℝ) (q x : ℝ) (b : ℤ) : ℝ :=
  if 0 ≤ b then markedActualMemoryProductAtom e q x b.toNat else 0

/-- The zero-extended actual product measure is nonnegative everywhere. -/
theorem markedMinorIntegerProductMass_nonneg_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ) (b : ℤ), 0 ≤ q → q ≤ 1 →
      0 ≤ markedMinorIntegerProductMass e q x b := by
  filter_upwards [marked_actual_memory_product_atom_nonneg_eventually e he] with x hx
  intro q b hq0 hq1
  unfold markedMinorIntegerProductMass
  split_ifs
  · exact hx q b.toNat hq0 hq1
  · exact le_rfl

/-- Exact conjugation, including the source 1/Y normalization and actual
endpoint cutoffs. -/
theorem markedMinorWeightedEndpointMatrix_scale {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (A : Matrix ι ι ℂ) (cut : ι → ℂ) {Y : ℝ} (hY : 0 < Y) :
    markedWeightedCountingMatrix mass (markedMinorEndpointMatrix ((Y : ℂ) • A) cut cut) =
      markedMinorEndpointMatrix A (fun i => cut i*(Real.sqrt (Y*mass i) : ℂ))
        (fun i => cut i*(Real.sqrt (Y*mass i) : ℂ)) := by
  ext i j
  rw [markedWeightedCountingMatrix_endpoint_scale mass _ hY]
  unfold markedMinorEndpointMatrix
  simp only [Matrix.smul_apply,smul_eq_mul]
  push_cast
  field_simp [show (Y : ℂ) ≠ 0 by exact_mod_cast hY.ne']

/-- On every integer support, the actual dyadic cutoff times the actual
square-root product mass is a bounded endpoint multiplier. -/
theorem markedMinorActualEndpoint_bound_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (b : ℤ), 0 ≤ q → q ≤ 1 → 0 < Y →
      ‖η ((b : ℝ)/Y)*(Real.sqrt (Y*markedMinorIntegerProductMass e q x b) : ℂ)‖ ≤
        Real.sqrt ((4/Real.log 2)^(Fintype.card J)) := by
  filter_upwards [marked_actual_memory_endpoint_cutoff_eventually e he hinj η hη] with x hx
  intro q Y b hq0 hq1 hY
  by_cases hcut : η ((b : ℝ)/Y)=0
  · rw [hcut,zero_mul,norm_zero]
    exact Real.sqrt_nonneg _
  · have hbY : Y ≤ (b : ℝ) := by
      have hh := (hη hcut).1
      simpa only [one_mul] using (le_div_iff₀ hY).mp hh
    have hb : 0 ≤ b := by exact_mod_cast hY.le.trans hbY
    have hbn : (b.toNat : ℝ)=(b : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hb
    have hm := hx q Y b.toNat hq0 hq1 hY (by simpa only [hbn] using hcut)
    rw [markedMinorIntegerProductMass,ite_eq_left hb]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_right (hηnorm _) (Real.sqrt_nonneg _)).trans
      (by simpa only [one_mul] using hm)

/-- The literal unnormalized position kernel, including both actual product
cutoffs, to be acted on with the actual pushed prime-product measure. -/
noncomputable def markedMinorActualCleanRawMatrix (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (D : ℕ) (Y Q : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ) : Matrix (P × S) (P × S) ℂ :=
  markedMinorEndpointMatrix ((Y : ℂ) • markedMinorPositionCleanProductMatrix ψ D Y Q P S)
    (fun i => η ((i.2.1 : ℝ)/Y)) (fun i => η ((i.2.1 : ℝ)/Y))

set_option maxHeartbeats 1000000 in
/-- Genuine clean-block decay with the actual PD prime-product measure.
The constant (4/log2)^K is proved from the actual growing moment and prime
bands, then absorbed. A0=G+4 depends only on G, not the band exponents. -/
theorem marked_minor_actual_memory_clean_opNorm {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c B R : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y r : ℝ) (D : ℕ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ) (z w : ℤ × ℤ),
      0 ≤ q → q ≤ 1 → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) → 0 < D → Squarefree D →
      markedMinorIntegerDet z w=1 →
      MarkedMinorShearGood ((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) Y →
      c ≤ |markedMinorIntegerTau r z| → |markedMinorIntegerTau r z| ≤ B →
      (∀ v ∈ P, c ≤ |markedMinorIntegerTau r v| ∧ |markedMinorIntegerTau r v| ≤ B) →
      (∀ v ∈ P, ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p z v) →
      (∀ v ∈ P, |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤ R*D*Y) →
      ‖markedWeightedCountingMatrix (fun i : P × S => markedMinorIntegerProductMass e q x i.2.1)
        (markedMinorActualCleanRawMatrix ψ η D Y ((Real.log x)^(G+4)) P S)‖ ≤ (Real.log x)^(-G) := by
  classical
  let C₀ := Real.sqrt ((4/Real.log 2)^(Fintype.card J))
  have hC₀ : 0 ≤ C₀ := Real.sqrt_nonneg _
  have hpos := marked_minor_position_clean_product_opNorm ψ (show 0<G+1 by linarith) hH hc hB hR
  simp only [show (G+1)+3=G+4 by ring] at hpos
  filter_upwards [Real.tendsto_log_atTop.eventually hpos,
    markedMinorActualEndpoint_bound_eventually e he hinj η hη hηnorm,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (C₀*C₀)))] with x hx hm hlog
  intro q Y r D P S z w hq0 hq1 hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hL : 0 < Real.log x := (by norm_num : (0:ℝ)<1).trans_le ((le_max_left _ _).trans hlog)
  have hCB : C₀*C₀ ≤ Real.log x := (le_max_right _ _).trans hlog
  unfold markedMinorActualCleanRawMatrix
  rw [markedMinorWeightedEndpointMatrix_scale _ _ _ hYp]
  have hnorm := markedMinorEndpointMatrix_norm_le
    (markedMinorPositionCleanProductMatrix ψ D Y ((Real.log x)^(G+4)) P S) _ _ hC₀ hC₀
    (fun i => hm q Y i.2.1 hq0 hq1 hYp) (fun i => hm q Y i.2.1 hq0 hq1 hYp)
  have hbase := hx Y r D P S z w hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell
  have hr : (Real.log x)^(-(G+1))=(Real.log x)^(-G)*(Real.log x)⁻¹ := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ ≤ (C₀*C₀)*‖markedMinorPositionCleanProductMatrix ψ D Y ((Real.log x)^(G+4)) P S‖ := hnorm
    _ ≤ (C₀*C₀)*(Real.log x)^(-(G+1)) := mul_le_mul_of_nonneg_left hbase (mul_nonneg hC₀ hC₀)
    _ ≤ (Real.log x)*(Real.log x)^(-(G+1)) := mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [hr]; field_simp

set_option maxHeartbeats 1000000 in
/-- The actual finite weighted clean action has the same squared-energy saving,
for arbitrary complex physical coefficients and the literal tilted measure. -/
theorem marked_minor_actual_memory_clean_energy {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c B R : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y r : ℝ) (D : ℕ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ) (z w : ℤ × ℤ),
      0 ≤ q → q ≤ 1 → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) → 0 < D → Squarefree D →
      markedMinorIntegerDet z w=1 →
      MarkedMinorShearGood ((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) Y →
      c ≤ |markedMinorIntegerTau r z| → |markedMinorIntegerTau r z| ≤ B →
      (∀ v ∈ P, c ≤ |markedMinorIntegerTau r v| ∧ |markedMinorIntegerTau r v| ≤ B) →
      (∀ v ∈ P, ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p z v) →
      (∀ v ∈ P, |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤ R*D*Y) →
      ∀ f : P × S → ℂ,
      (∑ i : P × S, markedMinorIntegerProductMass e q x i.2.1 *
        ‖markedWeightedMatrixApply (fun k : P × S => markedMinorIntegerProductMass e q x k.2.1)
          (markedMinorActualCleanRawMatrix ψ η D Y ((Real.log x)^(G+4)) P S) f i‖^2) ≤
        ((Real.log x)^(-G))^2 * ∑ i : P × S, markedMinorIntegerProductMass e q x i.2.1 * ‖f i‖^2 := by
  classical
  filter_upwards [marked_minor_actual_memory_clean_opNorm e he hinj ψ η hη hηnorm hG hH hc hB hR,
    markedMinorIntegerProductMass_nonneg_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hm hlog
  intro q Y r D P S z w hq0 hq1 hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell f
  exact markedWeightedMatrix_energy_le_of_counting_norm (ι := P × S)
    (fun i : P × S => markedMinorIntegerProductMass e q x i.2.1)
    (fun i => hm q i.2.1 hq0 hq1)
    (markedMinorActualCleanRawMatrix ψ η D Y ((Real.log x)^(G+4)) P S)
    (C := (Real.log x)^(-G)) (Real.rpow_nonneg (by linarith : (0:ℝ)≤Real.log x) _)
    (hx q Y r D P S z w hq0 hq1 hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell) f

end ArtinMatthews
