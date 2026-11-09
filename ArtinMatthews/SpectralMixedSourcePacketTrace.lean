module

public import ArtinMatthews.SpectralMixedPacketExpansion
public import ArtinMatthews.SpectralJMixedHolomorphicTrace
public import ArtinMatthews.SpectralABLMixedOppositeTrace
public import ArtinMatthews.SourceJHolomorphicPacket


set_option backward.privateInPublic true
@[expose] public section

/-! The actual forward traces apply to finite signed packets, including
the full same-sign holomorphic sector and all ambient sectors. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

def gamma0MixedSourcePacketSum {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero s] (hcop : r.Coprime s) (n : ℤ)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) : ℂ :=
  ∑ j ∈ v, α j*(∑' c, gamma0MixedSourceModulusTerm r s hcop (m j) n
    (fun C => f (4*Real.pi*Real.sqrt (|(m j : ℝ)*(n : ℝ)|)/C)) c)

theorem gamma0MixedSourcePacketSum_opposite_trace {ι : Type*}
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (hSign : ∀ j ∈ v, m j*n < 0) :
    gamma0MixedSourcePacketSum f r s hcop n v α m =
      (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r s b n*
        gamma0MixedPacketSpectralSide (r*s) (spectralABLOppositeEnergyTest f hf hc hp)
          (gamma0CuspOneOver s) Y hY n hn v α m hm := by
  let h := spectralABLOppositeEnergyTest f hf hc hp
  let A (j : ι) := gamma0BareSourceSpectralSide (r*s) h (gamma0CuspOneOver s) 1 Y hY n (m j) hn (hm j)
  let K := (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r s b n
  have hTrace (j : ι) (hj : j ∈ v) :=
    gamma0MixedABLOpposite_source_forward_trace r s hr hcop hab Y hY (m j) n (hm j) hn
      (hSign j hj) f hf hc hp
  have hExp := gamma0MixedPacketSpectralSide_eq_sum (r*s) h (gamma0CuspOneOver s) Y hY n hn v α m hm
    (fun j hj => (hTrace j hj).2.1.of_norm) (fun j hj => (hTrace j hj).2.2.1)
  calc
    _ = ∑ j ∈ v, α j*(K*A j) := by
      unfold gamma0MixedSourcePacketSum
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (α j*·) (hTrace j hj).2.2.2
    _ = K*(∑ j ∈ v, α j*A j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := congrArg (K*·) hExp.2.2.symm

theorem gamma0MixedSourcePacketSum_sameSign_trace {ι : Type*}
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (hSign : ∀ j ∈ v, 0 < m j*n) :
    let m₀ (j : ι) := sourceJHolomorphicIndexMagnitude (m j) (hm j)
    let n₀ := sourceJHolomorphicIndexMagnitude n hn
    gamma0MixedSourcePacketSum f r s hcop n v α m =
      gamma0MixedSourceCompensation r s b n*
        (4*gamma0MixedPacketSpectralSide (r*s) (spectralJClippedEnergyTest f hf hc hp)
          (gamma0CuspOneOver s) Y hY n hn v α m hm+
        sourceJHolomorphicMixedPacketSeries f r s hab (decide (n < 0)) v α m₀ n₀) := by
  let h := spectralJClippedEnergyTest f hf hc hp
  let A (j : ι) := gamma0BareSourceSpectralSide (r*s) h (gamma0CuspOneOver s) 1 Y hY n (m j) hn (hm j)
  let m₀ (j : ι) := sourceJHolomorphicIndexMagnitude (m j) (hm j)
  let n₀ := sourceJHolomorphicIndexMagnitude n hn
  let B (j : ι) := sourceJHolomorphicMixedGramSeries f r s hab (decide (n < 0)) (m₀ j) n₀
  let K := gamma0MixedSourceCompensation r s b n
  have hTrace (j : ι) (hj : j ∈ v) :=
    gamma0MixedABLJ_source_forward_trace r s hr hcop hab Y hY (m j) n (hm j) hn
      (hSign j hj) f hf hc hp
  have hExp := gamma0MixedPacketSpectralSide_eq_sum (r*s) h (gamma0CuspOneOver s) Y hY n hn v α m hm
    (fun j hj => (hTrace j hj).2.1.of_norm) (fun j hj => (hTrace j hj).2.2.1)
  have hHolo := sourceJHolomorphicMixedPacketSeries_linear f hf.continuous hc hp r s hr hcop hab
    (decide (n < 0)) v α m₀ n₀
  calc
    _ = ∑ j ∈ v, α j*(K*(4*A j+B j)) := by
      unfold gamma0MixedSourcePacketSum
      apply Finset.sum_congr rfl
      intro j hj
      have hs : decide (m j < 0) = decide (n < 0) := by
        rw [decide_eq_decide]
        rcases mul_pos_iff.mp (hSign j hj) with ⟨hm₁,hn₁⟩ | ⟨hm₁,hn₁⟩
        · exact iff_of_false (not_lt.mpr hm₁.le) (not_lt.mpr hn₁.le)
        · exact iff_of_true hm₁ hn₁
      have he := (hTrace j hj).2.2.2
      unfold sourceJHolomorphicSameSignGramSeries at he
      rw [hs] at he
      exact congrArg (α j*·) he
    _ = K*(4*(∑ j ∈ v, α j*A j)+∑ j ∈ v, α j*B j) := by
      rw [mul_add]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [← hExp.2.2]
      change _ * (4*_+∑ j ∈ v, α j*B j) = _
      rw [show (∑ j ∈ v, α j*B j) =
        sourceJHolomorphicMixedPacketSeries f r s hab (decide (n < 0)) v α m₀ n₀ from hHolo]

end ArtinMatthews
