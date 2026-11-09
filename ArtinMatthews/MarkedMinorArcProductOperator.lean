module

public import ArtinMatthews.MarkedMinorArcProductEnergy
public import ArtinMatthews.MarkedMinorArcCircle


set_option backward.privateInPublic true
@[expose] public section

/-! The literal minor-arc clean kernel on integer product supports. This
transports the checked determinant fiber bound back to counting measure. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Literal Fourier compression of a spatial matrix fiber to a finite
integer product support. -/
noncomputable def markedProductCompressionMatrix {ι : Type*} [Fintype ι]
    (S : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ) :
    Matrix (ι × S) (ι × S) ℂ :=
  fun hb la => ∫ θ : AddCircle (1:ℝ),
    fourier (la.2.1-hb.2.1) θ * F θ hb.1 la.1 ∂AddCircle.haarAddCircle

/-- The actual compressed matrix action is the Fourier coefficient of the
actual matrix fiber action. -/
theorem markedProductCompressionMatrix_mulVec {ι : Type*} [Fintype ι]
    (S : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ)
    (hFint : ∀ h l n, Integrable (fun θ : AddCircle (1:ℝ) =>
      fourier n θ * F θ h l) AddCircle.haarAddCircle)
    (c : ι → S → ℂ) (h : ι) (b : S) :
    (markedProductCompressionMatrix S F *ᵥ (fun la => c la.1 la.2)) (h,b) =
      ∫ θ : AddCircle (1:ℝ), fourier (-b.1) θ *
        markedProductFiberOutput S F c h θ ∂AddCircle.haarAddCircle := by
  classical
  change (∑ la : ι × S, (∫ θ : AddCircle (1:ℝ),
    fourier (la.2.1-b.1) θ * F θ h la.1 ∂AddCircle.haarAddCircle)*c la.1 la.2) = _
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun la _ => (hFint h la.1 (la.2.1-b.1)).mul_const (c la.1 la.2))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    change (∑ la : ι × S, fourier (la.2.1-b.1) θ * F θ h la.1 * c la.1 la.2) =
      fourier (-b.1) θ * markedProductFiberOutput S F c h θ
    rw [Fintype.sum_prod_type]
    simp only [markedProductFiberOutput,Matrix.mulVec,dotProduct,
      markedProductFourierPolynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro a _
    rw [sub_eq_add_neg,fourier_add]
    ring)

/-- Uniform spatial fiber decay gives the same actual compressed operator
norm, with no loss depending on the product support cardinality. -/
theorem markedProductCompressionMatrix_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hFmeas : ∀ h l, AEStronglyMeasurable (fun θ => F θ h l) AddCircle.haarAddCircle)
    (hFint : ∀ h l n, Integrable (fun θ : AddCircle (1:ℝ) =>
      fourier n θ * F θ h l) AddCircle.haarAddCircle)
    (hF : ∀ θ, ‖F θ‖ ≤ C) : ‖markedProductCompressionMatrix S F‖ ≤ C := by
  classical
  apply markedMinorMatrix_norm_le_of_energy _ hC
  intro c
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp_rw [markedProductCompressionMatrix_mulVec S F hFint (fun l a => c (l,a))]
  exact markedProductFiberOutput_fourier_energy S S F (fun l a => c (l,a)) hC hFmeas hF

/-- Every actual twisted minor-circle entry is absolutely integrable. -/
theorem markedMinorCircleFiber_twist_integrable (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ)
    (h l : MarkedMinorBoxIndex L T M N) (n : ℤ) :
    Integrable (fun θ : AddCircle (1:ℝ) => fourier n θ *
      markedMinorCircleFiber ψ L T M N Y Q θ h l) AddCircle.haarAddCircle := by
  classical
  have hc : Continuous (fun θ : AddCircle (1:ℝ) => fourier n θ *
      markedMinorSmoothCircleMatrix ψ L T M N Y θ h l) := by
    unfold markedMinorSmoothCircleMatrix
    fun_prop
  have hi : Integrable ((markedMinorCircleMajor Q Y)ᶜ.indicator
      (fun θ : AddCircle (1:ℝ) => fourier n θ *
        markedMinorSmoothCircleMatrix ψ L T M N Y θ h l)) AddCircle.haarAddCircle :=
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator
      (markedMinorCircleMajor_measurable Q Y).compl
  apply hi.congr
  exact Filter.Eventually.of_forall (fun θ => by
    by_cases hθ : θ ∈ markedMinorCircleMajor Q Y
    · simp [Set.indicator,markedMinorCircleFiber,hθ]
    · simp [Set.indicator,markedMinorCircleFiber,hθ])

/-- The literal clean kernel: determinant cutoff, normalized by Y, integrated
over the actual complement of major arcs, including the integer product phase. -/
noncomputable def markedMinorCleanProductMatrix (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ) (S : Finset ℤ) :
    Matrix (MarkedMinorBoxIndex L T M N × S) (MarkedMinorBoxIndex L T M N × S) ℂ :=
  markedProductCompressionMatrix S (markedMinorCircleFiber ψ L T M N Y Q)

/-- The actual finite clean minor-arc kernel has arbitrary logarithmic
operator-norm saving, uniformly in every integer product support. -/
theorem marked_minor_clean_product_opNorm (ψ : SchwartzMap ℝ ℂ) {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ) (S : Finset ℤ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      ‖markedMinorCleanProductMatrix ψ L T M N Y (Λ^(G+3)) S‖ ≤ Λ^(-G) := by
  classical
  filter_upwards [marked_minor_circle_fiber_opNorm ψ hG hC hH,
    Filter.eventually_ge_atTop (1:ℝ)] with Λ hΛ hΛone
  intro Y L T M N S hYlo hYhi hMpos hNpos hMN hM hN
  exact markedProductCompressionMatrix_opNorm S _
    (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Λ) _)
    (markedMinorCircleFiber_measurable ψ L T M N Y (Λ^(G+3)))
    (markedMinorCircleFiber_twist_integrable ψ L T M N Y (Λ^(G+3)))
    (hΛ Y L T M N hYlo hYhi hMpos hNpos hMN hM hN)

end ArtinMatthews
