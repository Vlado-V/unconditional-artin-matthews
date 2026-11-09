module

public import Mathlib.Analysis.InnerProductSpace.l2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded diagonal operators on actual Hilbert bases, with the exact
absolutely summable weighted coefficient pairing. -/
noncomputable section
open scoped InnerProductSpace lp
namespace ArtinMatthews

variable {ι : Type*}

def spectralLpDiagonalValue (w : ι → ℂ) (C : ℝ) (_hC : 0≤C) (hw : ∀ i,‖w i‖≤C)
    (f : lp (fun _ : ι => ℂ) 2) : lp (fun _ : ι => ℂ) 2 :=
  ⟨fun i => w i*f i, ((lp.memℓp f).norm.const_mul C).mono (fun i => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw i) (norm_nonneg (f i)))⟩

theorem spectralLpDiagonalValue_norm (w : ι → ℂ) (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C)
    (f : lp (fun _ : ι => ℂ) 2) : ‖spectralLpDiagonalValue w C hC hw f‖≤C*‖f‖ := by
  have h : ‖spectralLpDiagonalValue w C hC hw f‖≤‖C • f‖ :=
    lp.norm_mono (by norm_num) (fun i => by
      change ‖w i*f i‖≤‖C • f i‖
      rw [norm_mul,norm_smul,Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw i) (norm_nonneg (f i)))
  simpa only [norm_smul,Real.norm_of_nonneg hC] using h

def spectralLpDiagonal (w : ι → ℂ) (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := spectralLpDiagonalValue w C hC hw
      map_add' := by
        intro f g
        apply Subtype.ext
        funext i
        change w i*(f i+g i)=w i*f i+w i*g i
        ring
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext i
        change w i*(c*f i)=c*(w i*f i)
        ring }
    C (spectralLpDiagonalValue_norm w C hC hw)

theorem spectralLpDiagonal_apply (w : ι → ℂ) (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : spectralLpDiagonal w C hC hw f i=w i*f i := rfl

theorem spectralLpDiagonal_inner (w : ι → ℂ) (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C)
    (f g : lp (fun _ : ι => ℂ) 2) :
    inner ℂ f (spectralLpDiagonal w C hC hw g)=∑' i,w i*(inner ℂ (f i) (g i)) := by
  change (∑' i,inner ℂ (f i) (w i*g i))=_
  apply tsum_congr
  intro i
  simp only [RCLike.inner_apply]
  ring

theorem spectralLpDiagonal_pair_summable (w : ι → ℂ) (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C)
    (f g : lp (fun _ : ι => ℂ) 2) : Summable (fun i => w i*inner ℂ (f i) (g i)) := by
  have h := lp.summable_inner (𝕜:=ℂ) f (spectralLpDiagonal w C hC hw g)
  convert h using 1
  funext i
  change w i*inner ℂ (f i) (g i)=inner ℂ (f i) (w i*g i)
  simp only [RCLike.inner_apply]
  ring

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def spectralHilbertMultiplier (b : HilbertBasis ι ℂ H) (w : ι → ℂ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) : H →L[ℂ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((spectralLpDiagonal w C hC hw).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem spectralHilbertMultiplier_repr (b : HilbertBasis ι ℂ H) (w : ι → ℂ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) (x : H) (i : ι) :
    b.repr (spectralHilbertMultiplier b w C hC hw x) i=w i*b.repr x i := by
  change b.repr (b.repr.symm (spectralLpDiagonal w C hC hw (b.repr x))) i=_
  rw [b.repr.apply_symm_apply,spectralLpDiagonal_apply]

theorem spectralHilbertMultiplier_norm (b : HilbertBasis ι ℂ H) (w : ι → ℂ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) (x : H) :
    ‖spectralHilbertMultiplier b w C hC hw x‖≤C*‖x‖ := by
  change ‖b.repr.symm (spectralLpDiagonal w C hC hw (b.repr x))‖≤_
  rw [b.repr.symm.norm_map]
  exact (spectralLpDiagonalValue_norm w C hC hw (b.repr x)).trans_eq
    (congrArg (fun r : ℝ => C*r) (b.repr.norm_map x))

theorem spectralHilbertMultiplier_inner (b : HilbertBasis ι ℂ H) (w : ι → ℂ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) (x y : H) :
    inner ℂ x (spectralHilbertMultiplier b w C hC hw y)=
      ∑' i,w i*(inner ℂ x (b i)*inner ℂ (b i) y) := by
  rw [← b.repr.inner_map_map x (spectralHilbertMultiplier b w C hC hw y)]
  have he : b.repr (spectralHilbertMultiplier b w C hC hw y)=spectralLpDiagonal w C hC hw (b.repr y) := by
    apply Subtype.ext
    funext i
    exact spectralHilbertMultiplier_repr b w C hC hw y i
  rw [he,spectralLpDiagonal_inner]
  apply tsum_congr
  intro i
  rw [b.repr_apply_apply,b.repr_apply_apply,RCLike.inner_apply]
  have hconj : (starRingEnd ℂ) (inner ℂ (b i) x)=inner ℂ x (b i) := inner_conj_symm (𝕜:=ℂ) x (b i)
  rw [hconj]
  ring

theorem spectralHilbertMultiplier_pair_summable (b : HilbertBasis ι ℂ H) (w : ι → ℂ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ i,‖w i‖≤C) (x y : H) :
    Summable (fun i => w i*(inner ℂ x (b i)*inner ℂ (b i) y)) := by
  have h := spectralLpDiagonal_pair_summable w C hC hw (b.repr x) (b.repr y)
  convert h using 1
  funext i
  rw [b.repr_apply_apply,b.repr_apply_apply,RCLike.inner_apply]
  have hconj : (starRingEnd ℂ) (inner ℂ (b i) x)=inner ℂ x (b i) := inner_conj_symm (𝕜:=ℂ) x (b i)
  rw [hconj]
  ring

end Hilbert
end ArtinMatthews
