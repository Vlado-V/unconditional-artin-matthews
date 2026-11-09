module

public import ArtinMatthews.SourceKPAdelicEisensteinConvergence
public import Mathlib.Analysis.Complex.LocallyUniformLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Normal convergence and holomorphy of the actual Eisenstein family
in its initial right half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCompactEisenstein (s : ℂ) (q : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicEisensteinSum K hζ s (sourceKPAdelicCompactSection K hζ s) q

theorem sourceKPAdelicCompact_openCell_strip_bound (a b : ℝ)
    (ha : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*a+1)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (x : K) (s : ℂ) (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveWeyl K hζ *
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)‖ ≤
        (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) *
          Height.mulHeight₁ x ^ (-(2*a+1)) := by
  have hsr : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 := by linarith [hs.1]
  have hr : 0 ≤ s.re+1/2 := by
    have hn : 0 ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hc : (sourceKPAdelicHeightConstant K hζ g) ^ (s.re+1/2) ≤
      (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) := by
    calc
      _ ≤ (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (s.re+1/2) :=
        Real.rpow_le_rpow (sourceKPAdelicHeightConstant_pos K hζ g).le (le_max_right _ _) hr
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith [hs.2])
  have hx : Height.mulHeight₁ x ^ (-(2*s.re+1)) ≤ Height.mulHeight₁ x ^ (-(2*a+1)) :=
    Real.rpow_le_rpow_of_exponent_le (Height.one_le_mulHeight₁ x) (by linarith [hs.1])
  exact (sourceKPAdelicCompact_openCell_bound K hζ hsr q g hp x).trans
    (mul_le_mul hc hx (Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))

theorem sourceKPAdelicCompactEisenstein_holomorphic_strip (a b : ℝ)
    (ha : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*a+1)
    (q : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicCompactEisenstein K hζ s q)
      {s : ℂ | a < s.re ∧ s.re < b} := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  let U : Set ℂ := {s | a < s.re ∧ s.re < b}
  let F : K → ℂ → ℂ := fun x s => sourceKPAdelicCompactScalar K hζ s
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)
  let M : K → ℝ := fun x =>
    (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) * Height.mulHeight₁ x ^ (-(2*a+1))
  have hM : Summable M := (sourceKPRationalHeight_rpow_summable K ha).mul_left _
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hF : ∀ x, DifferentiableOn ℂ (F x) U := fun x =>
    (sourceKPAdelicCompactScalar_entire K hζ _).differentiableOn
  have hbound : ∀ x s, s ∈ U → ‖F x s‖ ≤ M x := by
    intro x s hs
    exact sourceKPAdelicCompact_openCell_strip_bound K hζ a b ha q g hg.symm x s ⟨hs.1.le,hs.2.le⟩
  have hsum : DifferentiableOn ℂ (fun s => ∑' x : K, F x s) U :=
    Complex.differentiableOn_tsum_of_summable_norm hM hF hU hbound
  have htotal := (sourceKPAdelicCompactScalar_entire K hζ q).differentiableOn.add hsum
  apply htotal.congr
  intro s hs
  have hsr : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 := by linarith [hs.1]
  exact sourceKPAdelicEisensteinSum_bruhat K hζ s (sourceKPAdelicCompactSection K hζ s) q
    (sourceKPAdelicCompactEisenstein_converges K hζ hsr q)

theorem sourceKPAdelicCompactEisenstein_holomorphic
    (q : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicCompactEisenstein K hζ s q)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  intro s hs
  let B : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  let a : ℝ := (s.re+(B-1)/2)/2
  let b : ℝ := s.re+1
  have ha : B ≤ 2*a+1 := by dsimp only [a]; change B < 2*s.re+1 at hs; linarith
  have has : a < s.re := by dsimp only [a]; change B < 2*s.re+1 at hs; linarith
  have hsb : s.re < b := by dsimp only [b]; linarith
  have hU : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  exact ((sourceKPAdelicCompactEisenstein_holomorphic_strip K hζ a b ha q).differentiableAt
    (hU.mem_nhds ⟨has,hsb⟩)).differentiableWithinAt

end
end ArtinMatthews
