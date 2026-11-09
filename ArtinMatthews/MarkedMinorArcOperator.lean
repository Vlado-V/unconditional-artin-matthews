module

public import ArtinMatthews.MarkedMinorArcClean
public import Mathlib.Analysis.CStarAlgebra.Matrix


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite determinant matrix and its L² operator norm.
The energy proof is transported to the genuine operator norm, with no
spectral bound supplied as an input. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The literal integer rectangle indexing the determinant matrix. -/
def markedMinorBox (L T : ℤ) (M N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Ico L (L+(M : ℤ))).product (Finset.Ico T (T+(N : ℤ)))

abbrev MarkedMinorBoxIndex (L T : ℤ) (M N : ℕ) := ↥(markedMinorBox L T M N)

/-- The actual normalized exponential matrix in the minor-arc fiber. -/
noncomputable def markedMinorDeterminantMatrix (L T : ℤ) (M N : ℕ) (Y θ : ℝ) :
    Matrix (MarkedMinorBoxIndex L T M N) (MarkedMinorBoxIndex L T M N) ℂ :=
  fun h l => ((Y : ℂ)⁻¹) * OAI.Problem337.RealPhase.phase
    (θ*((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1))

/-- Extend the actual finite coefficient vector by zero. -/
noncomputable def markedMinorBoxExtend {L T : ℤ} {M N : ℕ}
    (f : MarkedMinorBoxIndex L T M N → ℂ) (p : ℤ × ℤ) : ℂ :=
  if hp : p ∈ markedMinorBox L T M N then f ⟨p,hp⟩ else 0

@[simp] theorem markedMinorBoxExtend_apply {L T : ℤ} {M N : ℕ}
    (f : MarkedMinorBoxIndex L T M N → ℂ) (p : MarkedMinorBoxIndex L T M N) :
    markedMinorBoxExtend f p = f p := by simp only [markedMinorBoxExtend,dite_eq_left p.property]

/-- The finite matrix acts by the actual normalized determinant transform. -/
theorem markedMinorDeterminantMatrix_mulVec (L T : ℤ) (M N : ℕ) (Y θ : ℝ)
    (f : MarkedMinorBoxIndex L T M N → ℂ) (h : MarkedMinorBoxIndex L T M N) :
    (markedMinorDeterminantMatrix L T M N Y θ *ᵥ f) h =
      ((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N θ
        (markedMinorBoxExtend f) h.1.1 h.1.2 := by
  classical
  calc
    _ = ∑ l : MarkedMinorBoxIndex L T M N, ((Y : ℂ)⁻¹) *
        (markedMinorBoxExtend f l * OAI.Problem337.RealPhase.phase
          (θ*((h.1.1 : ℝ)*l.1.2-(h.1.2 : ℝ)*l.1.1))) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [markedMinorBoxExtend_apply]
      unfold markedMinorDeterminantMatrix
      ring
    _ = ∑ l ∈ markedMinorBox L T M N, ((Y : ℂ)⁻¹) *
        (markedMinorBoxExtend f l * OAI.Problem337.RealPhase.phase
          (θ*((h.1.1 : ℝ)*l.2-(h.1.2 : ℝ)*l.1))) :=
      Finset.sum_coe_sort (markedMinorBox L T M N) (fun l : ℤ × ℤ => ((Y : ℂ)⁻¹) *
        (markedMinorBoxExtend f l * OAI.Problem337.RealPhase.phase
          (θ*((h.1.1 : ℝ)*l.2-(h.1.2 : ℝ)*l.1))))
    _ = _ := by
      simp only [markedMinorBox,Finset.product_eq_sprod,Finset.sum_product,markedMinorDeterminantTransform,Finset.mul_sum]

theorem markedMinorMatrix_norm_le_of_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ f : ι → ℂ, (∑ i, ‖(A *ᵥ f) i‖^2) ≤ C^2*(∑ i, ‖f i‖^2)) :
    ‖A‖ ≤ C := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  exact henergy (WithLp.ofLp x)

/-- Actual operator-norm minor-arc decay, with the cutoff exponent `G+2`
independent of the marking-band exponents and fixed geometric constants. -/
theorem marked_minor_clean_determinant_opNorm {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ) (θ t : ℝ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      ¬MarkedInMajorArcs θ (Λ^(G+2)) Y → |t| ≤ Λ^(G+2)/2 →
      ‖markedMinorDeterminantMatrix L T M N Y (θ+t/Y)‖ ≤ Λ^(-G) := by
  classical
  filter_upwards [marked_minor_clean_determinant_energy hG hC hH,
    Filter.eventually_ge_atTop (1:ℝ)] with Λ henergy hΛ
  intro Y L T M N θ t hYlo hYhi hMpos hNpos hMN hM hN hminor ht
  have hΛp : 0 < Λ := by linarith
  apply markedMinorMatrix_norm_le_of_energy _ (Real.rpow_nonneg hΛp.le _)
  intro f
  have hh := henergy Y L T M N θ t (markedMinorBoxExtend f)
    hYlo hYhi hMpos hNpos hMN hM hN hminor ht
  have hleft : (∑ h : MarkedMinorBoxIndex L T M N,
      ‖(markedMinorDeterminantMatrix L T M N Y (θ+t/Y) *ᵥ f) h‖^2) =
      ∑ h₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ h₂ ∈ Finset.Ico T (T+(N : ℤ)),
        ‖((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N (θ+t/Y)
          (markedMinorBoxExtend f) h₁ h₂‖^2 := by
    simp_rw [markedMinorDeterminantMatrix_mulVec]
    calc
      _ = ∑ p ∈ markedMinorBox L T M N,
          ‖((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N (θ+t/Y)
            (markedMinorBoxExtend f) p.1 p.2‖^2 :=
        Finset.sum_coe_sort (markedMinorBox L T M N) _
      _ = _ := by
        change (∑ p ∈ (Finset.Ico L (L+(M:ℤ))).product (Finset.Ico T (T+(N:ℤ))), _) = _
        rw [Finset.product_eq_sprod,Finset.sum_product]
  have hright : (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)),
      ‖markedMinorBoxExtend f (l₁,l₂)‖^2) = ∑ l : MarkedMinorBoxIndex L T M N, ‖f l‖^2 := by
    calc
      _ = ∑ p ∈ markedMinorBox L T M N, ‖markedMinorBoxExtend f p‖^2 := by
        change _ = ∑ p ∈ (Finset.Ico L (L+(M:ℤ))).product (Finset.Ico T (T+(N:ℤ))), _
        rw [Finset.product_eq_sprod,Finset.sum_product]
      _ = ∑ p : MarkedMinorBoxIndex L T M N, ‖markedMinorBoxExtend f p‖^2 :=
        (Finset.sum_coe_sort (markedMinorBox L T M N) _).symm
      _ = _ := by simp only [markedMinorBoxExtend_apply]
  rw [hleft]
  rw [hright] at hh
  have he : Λ^(-2*G) = (Λ^(-G))^2 := by
    rw [← Real.rpow_mul_natCast hΛp.le]
    congr 1
    norm_num
    ring
  rw [he] at hh
  exact hh

end ArtinMatthews
