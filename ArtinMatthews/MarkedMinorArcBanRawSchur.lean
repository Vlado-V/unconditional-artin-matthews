module

public import ArtinMatthews.MarkedMinorArcBanRawEntry
public import ArtinMatthews.MarkedMinorArcBanRawRows
public import ArtinMatthews.MarkedMinorArcSchur
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ban removal in the tilted raw fiber and the unchanged-memory state. -/
noncomputable section
namespace ArtinMatthews

open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

def markedRawBanErrorBound (K pads : ℕ) (H A W Q x : ℝ) : ℝ :=
  H^2*markedBanErrorConstant K A W*(pads+1)*Q^3*Real.exp (-((Real.log x)^(1/10:ℝ)))

theorem markedRawBanErrorKernel_actual_schur_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (q r : ℝ)
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (complement : Z → ℤ × ℤ)
      (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ H A W : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ),
      0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ H → (∀ t, ‖η t‖ ≤ H) →
      (∀ s, ‖χ s‖ ≤ 1) → (∀ z : Z, markedMinorIntegerDet z.1 (complement z)=1) →
      (∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      1 ≤ Q → 1 ≤ Y → 0 ≤ A → 0 ≤ W →
      (∀ t, ‖ψ t‖ ≤ W) → (∀ t, ψ t ≠ 0 → |t| ≤ A) →
      ∀ bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B,
      ‖markedWeightedCountingMatrix
        (fun u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z =>
          markedRawLastMass (markedRawActualPrimeAtom e q x) u.2)
        (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg)‖ ≤
          markedRawBanErrorBound (Fintype.card J) pads H A W Q x := by
  classical
  filter_upwards [markedRawBanMajorant_actual_row_eventually e he hinj,
    markedBan_actual_typed_disjoint_eventually e hinj,
    marked_actual_tilted_atom_comparison_eventually e he] with x hrow hd ha
  intro pads B Z q r hZ complement ψ η d₀ Y Q ρ H A W χ hq0 hq1 hρ0 hρ1 hH hη hχ
    hdet hz hgeo hQ hY hA hW hψ hsupp bg
  let μ := fun u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z =>
    markedRawLastMass (markedRawActualPrimeAtom e q x) u.2
  let K := markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg
  let E := markedRawBanErrorBound (Fintype.card J) pads H A W Q x
  have hμ : ∀ u, 0 ≤ μ u := by
    intro u
    apply Finset.prod_nonneg
    intro j _
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (ha q hq0 hq1 j _).1
  have hE : 0 ≤ E := by dsimp [E,markedRawBanErrorBound,markedBanErrorConstant]; positivity
  have hr : ∀ u, ∑ v, μ v*‖K u v‖ ≤ E := by
    intro u
    calc
      _ ≤ ∑ v, μ v*(H^2*markedRawBanMajorant ψ Q Y bg u v) := by
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_left
          (markedRawBanErrorKernel_entry_norm_le hZ ψ η d₀ Y Q hρ0 hρ1 hH hη χ hχ bg u v) (hμ v)
      _ = H^2*∑ v, μ v*markedRawBanMajorant ψ Q Y bg u v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ ≤ H^2*(markedBanErrorConstant (Fintype.card J) A W*(pads+1)*Q^3*
          Real.exp (-((Real.log x)^(1/10:ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (hrow pads B Z q r complement ψ Q Y A W bg u hq0 hq1 hdet hz hgeo hQ hY hA hW hψ hsupp)
          (sq_nonneg H)
      _ = E := by dsimp [E,markedRawBanErrorBound]; ring
  have hc : ∀ v, ∑ u, μ u*‖K u v‖ ≤ E := by
    intro v
    obtain ⟨hψa,hsuppa⟩ := markedBanAdjointCutoff_bounds ψ hψ hsupp
    calc
      _ ≤ ∑ u, μ u*(H^2*markedRawBanMajorant (markedBanAdjointCutoff ψ) Q Y bg v u) := by
        apply Finset.sum_le_sum
        intro u _
        exact mul_le_mul_of_nonneg_left
          (markedRawBanErrorKernel_column_entry_norm_le hd hZ ψ η d₀ Y Q hρ0 hρ1 hH hη χ hχ bg u v) (hμ u)
      _ = H^2*∑ u, μ u*markedRawBanMajorant (markedBanAdjointCutoff ψ) Q Y bg v u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ ≤ H^2*(markedBanErrorConstant (Fintype.card J) A W*(pads+1)*Q^3*
          Real.exp (-((Real.log x)^(1/10:ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (hrow pads B Z q r complement (markedBanAdjointCutoff ψ) Q Y A W bg v hq0 hq1 hdet hz hgeo
            hQ hY hA hW hψa hsuppa) (sq_nonneg H)
      _ = E := by dsimp [E,markedRawBanErrorBound]; ring
  have hs := markedSchur_counting_norm_le μ (fun _ => 1) K hμ (fun _ => by norm_num)
    hE hE (by simpa only [mul_one] using hr) (by simpa only [mul_one] using hc)
  simpa only [Real.sqrt_mul_self hE] using hs

theorem markedRawCleanApply_energy_of_fiber_norm {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    {E : ℝ} (hE : 0 ≤ E)
    (hK : ∀ bg, ‖markedWeightedCountingMatrix
      (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2) (K bg)‖ ≤ E)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ s, markedRawStateMass ν s*‖markedRawCleanApply ν K f s‖^2) ≤
      E^2*∑ s, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  rw [markedRawCleanApply_energy_conditioned,markedRawState_energy_split ν pads B Z,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro bg _
  have hbg : 0 ≤ markedRawBackgroundMass ν bg := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun k _ => hν j _))
    · exact Finset.prod_nonneg (fun j _ => div_nonneg
        (Finset.prod_nonneg (fun k _ => hν j _)) (Nat.cast_nonneg _))
  have hh := markedWeightedMatrix_energy_le_of_counting_norm
    (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2)
    (fun u => Finset.prod_nonneg (fun j _ => hν j (u.2 j))) (K bg) hE (hK bg)
    (fun v => f ((markedRawStateSplit pads B Z).symm (bg,v)))
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at hh
  exact (mul_le_mul_of_nonneg_left hh hbg).trans_eq (by ring)

theorem markedRawBanErrorKernel_actual_energy_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (q r : ℝ)
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (complement : Z → ℤ × ℤ)
      (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ H A W : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ),
      0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ H → (∀ t, ‖η t‖ ≤ H) →
      (∀ s, ‖χ s‖ ≤ 1) → (∀ z : Z, markedMinorIntegerDet z.1 (complement z)=1) →
      (∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      1 ≤ Q → 1 ≤ Y → 0 ≤ A → 0 ≤ W →
      (∀ t, ‖ψ t‖ ≤ W) → (∀ t, ψ t ≠ 0 → |t| ≤ A) →
      ∀ f : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ,
      (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawCleanApply (markedRawActualPrimeAtom e q x)
          (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ) f s‖^2) ≤
        (markedRawBanErrorBound (Fintype.card J) pads H A W Q x)^2 *
          ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  classical
  filter_upwards [markedRawBanErrorKernel_actual_schur_eventually e he hinj,
    marked_actual_tilted_atom_comparison_eventually e he] with x hn ha
  intro pads B Z q r hZ complement ψ η d₀ Y Q ρ H A W χ hq0 hq1 hρ0 hρ1 hH hη hχ
    hdet hz hgeo hQ hY hA hW hψ hsupp f
  apply markedRawCleanApply_energy_of_fiber_norm (markedRawActualPrimeAtom e q x) ?_
    (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ) ?_ ?_ f
  · intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (ha q hq0 hq1 j _).1
  · unfold markedRawBanErrorBound markedBanErrorConstant
    positivity
  · exact hn pads B Z q r hZ complement ψ η d₀ Y Q ρ H A W χ hq0 hq1 hρ0 hρ1 hH hη hχ
      hdet hz hgeo hQ hY hA hW hψ hsupp

end ArtinMatthews
