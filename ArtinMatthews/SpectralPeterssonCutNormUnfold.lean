module

public import ArtinMatthews.SpectralModularPartitionGamma0
public import ArtinMatthews.SpectralPeterssonCutPacket
public import ArtinMatthews.SpectralPeterssonGammaTail
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralPeterssonCutPacketMass
public import ArtinMatthews.SpectralPeterssonRealUnfold
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

/-! Exact integration of the actual cut-packet row mass over the native
Gamma0 region. Both central representatives are retained in the cover. -/
noncomputable section
open Set MeasureTheory Matrix UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

theorem gamma0PeterssonCutPacket_row_mass (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    (A : ℝ) (hA : 0 ≤ A) (hn : Set.InjOn n (t : Set ι)) :
    (∫ z in gamma0InteriorRegion N, ∑' p : Gamma0PeterssonSignedRow N 1 a,
      ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k) =
      2*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) := by
  let σ := (gamma0TrueCuspScaling N a)⁻¹
  let G (z : UpperHalfPlane) := ‖spectralPeterssonStripCutPacket k t α n A z‖^2*z.im^k
  let F (z : UpperHalfPlane) := G (σ • z)
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => σ • z) volume volume := by
    change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ • z) _ _
    exact measurePreserving_smul _ _
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => σ • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ • z)
    exact measurableEmbedding_const_smul _
  have hG : Integrable G := spectralPeterssonStripCutPacket_norm_integrable k hk t α n A
  have hF : Integrable F := hpres.integrable_comp_of_integrable (g := G) hG
  have hFi : (∫ z, F z) = spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2 := by
    change (∫ z, G (σ • z)) = _
    rw [hpres.integral_comp hemb G]
    exact spectralPeterssonStripCutPacket_mass k hk t α n A hA hn
  have hpoint (z : UpperHalfPlane) :
      (∑' p : Gamma0PeterssonSignedRow N 1 a,
        ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k) =
        ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z) := by
    rw [gamma0PeterssonCutPacket_square_periodization]
    calc
      _ = ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val • z) := by
        apply tsum_congr
        intro γ
        simp only [F,G,σ,mul_smul,atkinRealMap_smul]
      _ = _ := by
        simpa only [Equiv.inv_apply,Subgroup.coe_inv] using
          ((Equiv.inv (CongruenceSubgroup.Gamma0 N)).tsum_eq
            (fun γ : CongruenceSubgroup.Gamma0 N => F (γ.val • z))).symm
  simp_rw [hpoint]
  rw [gamma0PeterssonRegion_real_integral_unfold N F hF,hFi]

theorem gamma0PeterssonCutPacket_row_integrable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    (A : ℝ) (hA : 0 ≤ A) (hn : Set.InjOn n (t : Set ι)) :
    IntegrableOn (fun z => ∑' p : Gamma0PeterssonSignedRow N 1 a,
      ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k) (gamma0InteriorRegion N) := by
  classical
  by_cases hα : ∀ j ∈ t, α j = 0
  · have hz (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) :
        gamma0PeterssonCutPacketRow N a k t α n A p z = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hα j hj,zero_mul,zero_mul]
    simp only [hz,norm_zero,zero_pow (by omega : 2 ≠ 0),zero_mul,tsum_zero]
    exact integrableOn_zero
  · push_neg at hα
    obtain ⟨j,hj,hjα⟩ := hα
    have hsum : 0 < ∑ i ∈ t, ‖α i‖^2 :=
      Finset.sum_pos' (fun i hi => sq_nonneg _) ⟨j,hj,sq_pos_of_pos (norm_pos_iff.mpr hjα)⟩
    have hratio : 0 < spectralPeterssonGammaTailRatio k A :=
      (Real.exp_pos (-A)).trans_le (spectralPeterssonGammaTailRatio_bounds k hk A hA).1
    apply Integrable.of_integral_ne_zero
    rw [gamma0PeterssonCutPacket_row_mass N a k hk t α n A hA hn]
    exact ne_of_gt (by positivity)

end ArtinMatthews
