module

public import ArtinMatthews.SpectralPeterssonCutPacket


set_option backward.privateInPublic true
@[expose] public section

/-! Sharp-cut seeds and their actual countable Poincare sums are measurable. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

theorem spectralPeterssonHeightCutSeed_measurable (n : ℕ+) (A : ℝ) :
    Measurable (spectralPeterssonHeightCutSeed n A) := by
  have hs : MeasurableSet {z : UpperHalfPlane | A < 4*Real.pi*(n : ℝ)*z.im} := by
    apply measurableSet_lt measurable_const
    fun_prop
  have hf : Continuous (spectralHolomorphicCuspSeed (n : ℕ)) := by
    unfold spectralHolomorphicCuspSeed
    fun_prop
  exact Measurable.ite hs hf.measurable measurable_const

theorem spectralHolomorphicSlash_measurable (k : ℕ) (G : SL(2, ℝ))
    {F : UpperHalfPlane → ℂ} (hF : Measurable F) :
    Measurable (spectralHolomorphicSlash k G F) := by
  have he : spectralHolomorphicSlash k G F = fun z : UpperHalfPlane =>
      F (G • z)/(((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ))^k :=
    funext (spectralHolomorphicSlash_apply k G F)
  rw [he]
  apply Measurable.div
  · exact hF.comp (by fun_prop)
  · fun_prop

theorem gamma0PeterssonCutRow_measurable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (p : Gamma0PeterssonSignedRow N 1 a) :
    Measurable (gamma0PeterssonCutRow N a k n A p) := by
  have he : gamma0PeterssonCutRow N a k n A p =
      spectralHolomorphicSlash k (gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val)
        (spectralPeterssonHeightCutSeed n A) :=
    funext (gamma0PeterssonCutRow_eq_slash N a k n A p)
  rw [he]
  exact spectralHolomorphicSlash_measurable k _ (spectralPeterssonHeightCutSeed_measurable n A)

theorem gamma0PeterssonCutPacket_measurable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) {A : ℝ} (hA : 0 < A) :
    Measurable (gamma0PeterssonCutPacket N a k t α n A) := by
  classical
  letI : Countable (Gamma0PeterssonSignedRow N 1 a) := by
    unfold Gamma0PeterssonSignedRow
    infer_instance
  have hp (p : Gamma0PeterssonSignedRow N 1 a) :
      Measurable (fun z => gamma0PeterssonCutPacketRow N a k t α n A p z) := by
    unfold gamma0PeterssonCutPacketRow
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.mul (gamma0PeterssonCutRow_measurable N a k (n j) A p)
  have he : gamma0PeterssonCutPacket N a k t α n A =
      fun z => (1/2 : ℂ)*∑' p : Gamma0PeterssonSignedRow N 1 a,
        gamma0PeterssonCutPacketRow N a k t α n A p z :=
    funext (gamma0PeterssonCutPacket_eq_rows N a k t α n hA)
  rw [he]
  exact measurable_const.mul (Measurable.tsum hp)

end ArtinMatthews
