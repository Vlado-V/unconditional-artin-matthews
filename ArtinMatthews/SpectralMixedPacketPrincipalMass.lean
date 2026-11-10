module

public import ArtinMatthews.SpectralJPrincipalMass
public import ArtinMatthews.SpectralInfinityComplementaryCusp
public import ArtinMatthews.SpectralInfinityPrincipalCutoffBessel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual cusp cutoff masses on the principal spectral subtype. -/

noncomputable section
open Set OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0InfinityPacketPrincipalDensity {ι : Type*} (N : ℕ) [NeZero N]
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (i : Gamma0HeatPrincipalCuspidalIndex N) : ℝ :=
  ‖gamma0InfinityCuspPacketAmplitude N i.val v α m hm Y hY‖^2/
    Real.cosh (Real.pi*gamma0CuspPrincipalParameter N i.val)

private def cutoffIndices (N : ℕ) [NeZero N] (u : Finset (Gamma0HeatPrincipalCuspidalIndex N))
    (R : ℝ) : Finset (Gamma0AllHeightSpectralIndex N) := by
  classical
  exact (u.filter (fun i => 1+|gamma0CuspPrincipalParameter N i.val| ≤ R)).map
    ⟨Subtype.val,Subtype.val_injective⟩

private theorem cutoffIndices_spec (N : ℕ) [NeZero N] (u : Finset (Gamma0HeatPrincipalCuspidalIndex N))
    (R : ℝ) (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ cutoffIndices N u R) :
    1/4 ≤ gamma0AllHeightGradientSpectralValue N i ∧
      1+|gamma0CuspPrincipalParameter N i| ≤ R := by
  classical
  unfold cutoffIndices at hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  exact ⟨j.property,(Finset.mem_filter.mp hj).2⟩

theorem gamma0Infinity_packet_principal_density_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ {B Y : ℝ}, 0 < B → ∀ hY : 0 < Y, Y < (1/16)/B →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      ∀ (u : Finset (Gamma0HeatPrincipalCuspidalIndex N)) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter N j.val| ≤ R),
        gamma0InfinityPacketPrincipalDensity N v α m hm Y hY i) ≤
        (C*(∑ j ∈ v, ‖α j‖^2))*(R^2+(B/(N : ℝ))*R) := by
  classical
  obtain ⟨C,hC,hCut⟩ := gamma0Infinity_principal_cutoff_orbit_bessel
  refine ⟨C,hC,?_⟩
  intro ι N inst v α m hm hinj B Y hB hY hYL hfreq u R hR
  have h := hCut N (cutoffIndices N u R) v α m hinj hm hR hB hY hYL hfreq
    (fun i hi => (cutoffIndices_spec N u R i hi).1) (fun i hi => (cutoffIndices_spec N u R i hi).2)
  have hs := h.trans_eq (show C*(R^2+B*R/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2) =
    (C*(∑ j ∈ v, ‖α j‖^2))*(R^2+(B/(N : ℝ))*R) by ring)
  simpa only [cutoffIndices,Finset.sum_map,Function.Embedding.coeFn_mk,
    gamma0InfinityPacketPrincipalDensity,gamma0InfinityCuspPacketAmplitude,
    gamma0CuspPrincipalParameter] using hs

private theorem cutoffIndices_moment_eq (N : ℕ) [NeZero N]
    (u : Finset (Gamma0HeatPrincipalCuspidalIndex N)) (R : ℝ)
    (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspPrincipalMoment N (cutoffIndices N u R) b Y hY n hn =
      ∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter N j.val| ≤ R),
        gamma0NativePrincipalDensity N b Y hY n hn i := by
  classical
  unfold gamma0CuspPrincipalMoment cutoffIndices
  rw [Finset.sum_map]
  rfl

theorem gamma0NativePrincipalDensity_cutoff_of_moment
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (u : Finset (Gamma0HeatPrincipalCuspidalIndex N)) (R M : ℝ)
    (hMom : ∀ V : Finset (Gamma0AllHeightSpectralIndex N),
      (∀ i ∈ V, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) →
      (∀ i ∈ V, 1+|gamma0CuspPrincipalParameter N i| ≤ R) →
      gamma0CuspPrincipalMoment N V b Y hY n hn ≤ M) :
    (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter N j.val| ≤ R),
      gamma0NativePrincipalDensity N b Y hY n hn i) ≤ M := by
  have h := hMom (cutoffIndices N u R)
    (fun i hi => (cutoffIndices_spec N u R i hi).1) (fun i hi => (cutoffIndices_spec N u R i hi).2)
  exact (cutoffIndices_moment_eq N u R b Y hY n hn).symm.trans_le h

end ArtinMatthews
