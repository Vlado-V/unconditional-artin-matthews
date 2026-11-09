module

public import ArtinMatthews.MarkedMinorArcLatticeBox
public import ArtinMatthews.MarkedMinorArcCompression
public import ArtinMatthews.MarkedMinorArcEndpoints


set_option backward.privateInPublic true
@[expose] public section

/-! The actual clean minor kernel on arbitrary finite good-state sheared
lattice supports, transported by an actual determinant-one integer basis. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Literal clean determinant kernel on the original integer lattice points,
before the good-state change of basis. -/
noncomputable def markedMinorShearCleanProductMatrix (ψ : SchwartzMap ℝ ℂ)
    (Y Q : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ) : Matrix (P × S) (P × S) ℂ :=
  fun pb qa => ((Y : ℂ)⁻¹)*ψ (((pb.1.1.1*qa.1.1.2-pb.1.1.2*qa.1.1.1 : ℤ) : ℝ)/Y) *
    ∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier ((pb.1.1.1*qa.1.1.2-pb.1.1.2*qa.1.1.1)-pb.2.1+qa.2.1) θ ∂AddCircle.haarAddCircle

/-- Exact basis transport gives a principal restriction of the checked box
kernel; determinant normalization and every product phase are unchanged. -/
theorem markedMinorShearCleanProductMatrix_submatrix (ψ : SchwartzMap ℝ ℂ)
    (Y Q : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ)
    (h l a b L T : ℤ) (M N : ℕ) (hd : h*b-l*a=1)
    (hP : ∀ p : P, markedMinorBasisCoords h l a b p.1 ∈ markedMinorBox L T M N) :
    ∃ e : (P × S) → (MarkedMinorBoxIndex L T M N × S), Function.Injective e ∧
      markedMinorShearCleanProductMatrix ψ Y Q P S =
        (markedMinorCleanProductMatrix ψ L T M N Y Q S).submatrix e e := by
  classical
  let e : (P × S) → (MarkedMinorBoxIndex L T M N × S) :=
    fun pb => (⟨markedMinorBasisCoords h l a b pb.1.1,hP pb.1⟩,pb.2)
  refine ⟨e,?_,?_⟩
  · intro pb qa he
    have h₁ := congrArg (fun z => z.1.1) he
    have h₂ := congrArg Prod.snd he
    have hh := markedMinorBasisCoords_injective h l a b hd h₁
    exact Prod.ext (Subtype.ext hh) h₂
  · ext pb qa
    rw [Matrix.submatrix_apply,markedMinorCleanProductMatrix_apply]
    change ((Y : ℂ)⁻¹)*ψ (((pb.1.1.1*qa.1.1.2-pb.1.1.2*qa.1.1.1 : ℤ) : ℝ)/Y) *
        (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
          fourier ((pb.1.1.1*qa.1.1.2-pb.1.1.2*qa.1.1.1)-pb.2.1+qa.2.1) θ ∂AddCircle.haarAddCircle) = _
    simp only [markedMinorBasisCoords_determinant h l a b hd]

/-- Genuine minor-arc clean decay on every finite good-state shear support.
The actual determinant kernel and coefficients are retained, and there is
no loss in either the spatial or integer product support cardinality. -/
theorem marked_minor_shear_clean_product_opNorm (ψ : SchwartzMap ℝ ℂ) {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y α : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      MarkedMinorShearGood α Y →
      (∀ p ∈ P, |(p.1 : ℝ)+(p.2 : ℝ)*α| ≤ C ∧ |(p.2 : ℝ)/Y| ≤ C) →
      ‖markedMinorShearCleanProductMatrix ψ Y (Λ^(G+3)) P S‖ ≤ Λ^(-G) := by
  classical
  have hgeom : 1 ≤ 300*C^2 := by nlinarith [sq_nonneg (C-1)]
  filter_upwards [marked_minor_clean_product_opNorm ψ hG hgeom hH,
    Filter.eventually_ge_atTop (1:ℝ)] with Λ hΛ hΛone
  intro Y α P S hYlo hYhi hg hP
  have hY : 1 ≤ Y := (Real.one_le_exp_iff.mpr (Real.rpow_nonneg (by linarith : (0:ℝ)≤Λ) _)).trans hYlo
  obtain ⟨h,l,a,b,L,T,M,N,hd,hMlo,hNlo,hMN,hM,hN,hpoints⟩ :=
    markedMinorShear_good_integer_box α hY hC hg
  have hMp : 1 ≤ M := by exact_mod_cast (Real.one_le_rpow hY (by norm_num : (0:ℝ)≤1/10)).trans hMlo
  have hNp : 1 ≤ N := by exact_mod_cast (Real.one_le_rpow hY (by norm_num : (0:ℝ)≤1/10)).trans hNlo
  have hC₀ : 0 ≤ 300*C^2 := by positivity
  have hMgeom : (M : ℝ) ≤ (300*C^2)*Y^(9/10 : ℝ) :=
    hM.trans (mul_le_mul (by nlinarith [sq_nonneg (C-1)] : 30*C≤300*C^2)
      (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity) hC₀)
  have hNgeom : (N : ℝ) ≤ (300*C^2)*Y^(9/10 : ℝ) :=
    hN.trans (mul_le_mul (by nlinarith [sq_nonneg (C-1)] : 20*C≤300*C^2)
      (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity) hC₀)
  obtain ⟨e,he,heq⟩ := markedMinorShearCleanProductMatrix_submatrix ψ Y (Λ^(G+3)) P S
    h l a b L T M N hd (fun p => hpoints p (hP p p.2).1 (hP p p.2).2)
  rw [heq]
  exact (markedMinorSubmatrix_injective_norm_le _ e he).trans
    (hΛ Y L T M N S hYlo hYhi hMp hNp hMN hMgeom hNgeom)

end ArtinMatthews
