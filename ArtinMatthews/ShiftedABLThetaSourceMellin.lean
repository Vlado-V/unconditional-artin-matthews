module

public import ArtinMatthews.ShiftedABLMellinCircle


set_option backward.privateInPublic true
@[expose] public section

/-! The finite signed circle blocks for the actual shifted cutoff and
fixed plateau have the exact Mellin representation with controlled moments. -/

noncomputable section
open MeasureTheory Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

theorem shiftedABLThetaSignedCircleBlock_source_mellin
    (A J : ℕ) (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
        (T m1 m2 : ℝ) (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)),
        0 < m1 → 0 < m2 → 1 ≤ m1*T → 1 ≤ m2*T →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        ∀ (D m3 m4 F r L : ℕ), 0 < F → 0 < L → ∀ (d : ℕ × ℕ),
        let Q : ℝ := 3*(L : ℝ)
        let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
        let W1 := shiftedABLThetaTestWeight g hg T m1 hT hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        ∃ b1 b2 : SchwartzMap ℝ ℂ,
          (1+(m1*T)*((2 : ℝ)^d.1/Q^2))^A *
            (∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖) ≤ C*(m1*T) ∧
          (1+(m2*T)*((2 : ℝ)^d.2/Q^2))^A *
            (∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖) ≤ C*(m2*T) ∧
          ∀ i : ℕ × Bool,
            let f (z : ℝ × ℝ) :=
              shiftedABLMellinSignedSum χ D m3 m4 F r L d i z*(b1 z.1*b2 z.2)
            Integrable f ∧
              shiftedABLThetaSignedCircleBlock χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L d i =
                (cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4) /
                  ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))) * ∫ z : ℝ × ℝ, f z := by
  obtain ⟨C,hC,hkernels⟩ := shiftedABLSource_mellin_kernels A J Cg hCg
  refine ⟨C,hC,?_⟩
  intro χ g hg T m1 m2 hT hgs hm1 hm2 hs1 hs2 hderiv D m3 m4 F r L hF hL d Q Λ W1 W2
  have hQ : 0 < Q := by
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    change 0 < 3*(L : ℝ)
    positivity
  obtain ⟨b1,b2,h1,h2,hb1,hb2⟩ :=
    hkernels g hg T m1 m2 hT hm1 hm2 hgs hs1 hs2 hderiv Q hQ d.1 d.2
  refine ⟨b1,b2,hb1,hb2,?_⟩
  intro i
  have hband (q : ℕ) (hq : q ∈ circleModuli F r L) : Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*Q := by
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    refine ⟨by change 3*(L : ℝ) ≤ (q : ℝ); exact_mod_cast hlo, ?_⟩
    calc
      _ ≤ ((6*L : ℕ) : ℝ) := by exact_mod_cast hhi
      _ = _ := by change _ = 2*(3*(L : ℝ)); push_cast; ring
  have hW1 : (fun x : ℝ => W1 (x/(m1*T))) = shiftedSourceTest g m1 := by
    funext x
    exact (shiftedSourceTest_eq_normalized g hg T m1 hT hm1 hgs x).symm
  have hW2 : (fun x : ℝ => W2 (x/(m2*T))) = shiftedSourceMajorant m2 T := by
    funext x
    exact (shiftedSourceMajorant_eq_normalized m2 T x).symm
  apply shiftedABLThetaSignedCircleBlock_eq_mellin χ W1 W2 (m1*T) (m2*T)
    D m3 m4 F r L hF hL d i b1 b2
  · intro q hq k hk
    rw [hW1]
    exact h1 k (by have := (Finset.mem_Icc.mp hk).1; omega) q (hband q hq).1 (hband q hq).2
  · intro q hq k hk
    rw [hW2]
    exact h2 k (by have := (Finset.mem_Icc.mp hk).1; omega) q (hband q hq).1 (hband q hq).2

end ArtinMatthews
