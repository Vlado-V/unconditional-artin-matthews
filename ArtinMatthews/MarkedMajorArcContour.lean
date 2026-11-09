module

public import ArtinMatthews.MarkedMajorArcMangoldt
public import ArtinMatthews.MarkedMajorArcZeroFree


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite contour identities for the actual Perron kernel. The only
kernel pole in the strip `-1 < Re z` is at zero, and its residue is `F 0`.
This residue cancels under the two endpoint differences in the smoothing. -/
namespace ArtinMatthews

open Complex Set Filter Asymptotics Erdos970
open scoped Topology

lemma marked_perron_kernel_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s ≠ 0) (hs1 : s+1 ≠ 0) :
    DifferentiableAt ℂ (markedPerronKernel x) s := by
  unfold markedPerronKernel
  apply DifferentiableAt.div
  · exact ((hasDerivAt_id s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt
  · fun_prop
  · exact mul_ne_zero hs hs1

lemma marked_perron_product_simple_pole {x : ℝ} (hx : 0 < x)
    {F : ℂ → ℂ} (hF : DifferentiableAt ℂ F 0) :
    ((fun s => F s*markedPerronKernel x s) - (fun s => F 0/s))
      =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
  let g : ℂ → ℂ := fun s => F s*(x:ℂ)^s/(s+1)
  have hg : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div
    · exact hF.mul (((hasDerivAt_id (0:ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt)
    · fun_prop
    · norm_num
  have hg0 : g 0 = F 0 := by simp [g]
  have hh := hg.isBigO_sub.mono (show 𝓝[≠] (0:ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨C,_,hC⟩ := hh.exists_nonneg
  apply IsBigO.of_bound C
  filter_upwards [hC.bound,self_mem_nhdsWithin] with s hs hn
  change s ≠ 0 at hn
  simp only [sub_zero, hg0] at hs
  have he : F s*markedPerronKernel x s - F 0/s = (g s-F 0)/s := by
    dsimp [markedPerronKernel,g]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simp only [Pi.sub_apply,Pi.one_apply,norm_one,mul_one]
  rw [he,norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr hs

/-- An exact rectangle residue identity, ready for the proved character
rectangle. In particular this is the kernel residue, not a residue from
an incorrectly crossed L-function zero or principal pole. -/
theorem marked_perron_product_rectangle {x a b T : ℝ}
    (hx : 0 < x) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b) (hT : 0 < T)
    {F : ℂ → ℂ}
    (hF : ∀ s ∈ Rectangle ((a:ℂ)-Complex.I*(T:ℂ)) ((b:ℂ)+Complex.I*(T:ℂ)),
      DifferentiableAt ℂ F s) :
    RectangleIntegral' (fun s => F s*markedPerronKernel x s)
      ((a:ℂ)-Complex.I*(T:ℂ)) ((b:ℂ)+Complex.I*(T:ℂ)) = F 0 := by
  have hab : a ≤ b := by linarith
  have hp : Rectangle ((a:ℂ)-Complex.I*(T:ℂ)) ((b:ℂ)+Complex.I*(T:ℂ)) ∈ 𝓝 (0:ℂ) := by
    rw [rectangle_mem_nhds_iff]
    simpa [Complex.mem_reProdIm,uIoo_of_le hab,uIoo_of_le (show -T ≤ T by linarith),
      Complex.mul_re,Complex.mul_im] using
      (show (a < 0 ∧ 0 < b) ∧ -T < 0 ∧ 0 < T from ⟨⟨ha0,hb⟩,by linarith,hT⟩)
  apply ResidueTheoremOnRectangleWithSimplePole' (p := 0)
  · simpa using hab
  · simp
    linarith
  · exact hp
  · intro s hs
    have hsr : a ≤ s.re := by
      have hh : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
        simpa [Rectangle,Complex.mem_reProdIm,uIcc_of_le hab,
          uIcc_of_le (show -T ≤ T by linarith)] using hs.1
      exact hh.1.1
    have hs0 : s ≠ 0 := by simpa using hs.2
    have hs1 : s+1 ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      linarith
    exact ((hF s hs.1).mul (marked_perron_kernel_differentiableAt hx hs0 hs1)).differentiableWithinAt
  · simpa only [sub_zero] using marked_perron_product_simple_pole hx (hF 0 (mem_of_mem_nhds hp))

lemma marked_character_logderiv_differentiableAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z s : ℂ}
    (hs : s+z ≠ 1) (hn : DirichletCharacter.LFunction χ (s+z) ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => -deriv (DirichletCharacter.LFunction χ) (w+z) /
      DirichletCharacter.LFunction χ (w+z)) s := by
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
  have ha := han (s+z) hs
  have hadd : DifferentiableAt ℂ (fun w : ℂ => w+z) s := by fun_prop
  exact ((ha.deriv.differentiableAt.comp s hadd).neg.div
    (ha.differentiableAt.comp s hadd) hn)

/-- Exact finite contour shift for the actual character Mangoldt integrand.
The frequency condition excludes the principal-character pole throughout. -/
theorem marked_major_mangoldt_rectangle {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x a b T t : ℝ}
    (hx : 0 < x) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b) (hT : 0 < T)
    (ht : T < |t|)
    (hzero : ∀ s ∈ Rectangle ((a:ℂ)-Complex.I*(T:ℂ)) ((b:ℂ)+Complex.I*(T:ℂ)),
      DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I)) ≠ 0) :
    RectangleIntegral' (markedMajorMangoldtIntegrand χ x t)
      ((a:ℂ)-Complex.I*(T:ℂ)) ((b:ℂ)+Complex.I*(T:ℂ)) =
      -deriv (DirichletCharacter.LFunction χ) (1-(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction χ (1-(t:ℂ)*Complex.I) := by
  have hab : a ≤ b := by linarith
  have he := marked_perron_product_rectangle hx ha ha0 hb hT
    (F := fun s => -deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
      DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I))) ?_
  · change RectangleIntegral' (fun s => (-deriv (DirichletCharacter.LFunction χ)
      (s+(1-(t:ℂ)*Complex.I)) / DirichletCharacter.LFunction χ
      (s+(1-(t:ℂ)*Complex.I))) * markedPerronKernel x s) _ _ = _
    simpa only [zero_add] using he
  intro s hs
  have him : |s.im| ≤ T := by
    have hh : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle,Complex.mem_reProdIm,uIcc_of_le hab,
        uIcc_of_le (show -T ≤ T by linarith)] using hs
    exact abs_le.mpr hh.2
  apply marked_character_logderiv_differentiableAt χ _ (hzero s hs)
  intro heq
  have heqim := congrArg Complex.im heq
  simp only [Complex.add_im,Complex.sub_im,Complex.one_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_one,mul_zero,add_zero,zero_sub] at heqim
  have heqt : s.im = t := by linarith
  rw [heqt] at him
  exact (not_lt_of_ge him) ht

/-- The preceding contour identity on a rectangle supplied by the proved
unconditional character estimate. The remaining hypotheses are only explicit
frequency, modulus and contour-height ranges. -/
theorem marked_major_mangoldt_uniform_rectangle (A b : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∃ K T₀ : ℝ, 0 < K ∧ 0 < T₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (x t H : ℝ),
      0 < x → 0 < H → H ≤ |t|/2 → 2*T₀ ≤ |t| →
      2*|t| ≤ Real.exp (b*L) →
      RectangleIntegral' (markedMajorMangoldtIntegrand χ x t)
        (((-L^(-(3/4:ℝ)):ℝ):ℂ)-Complex.I*(H:ℂ))
        (((1/L:ℝ):ℂ)+Complex.I*(H:ℂ)) =
        -deriv (DirichletCharacter.LFunction χ) (1-(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction χ (1-(t:ℂ)*Complex.I) ∧
      ∀ s ∈ Rectangle
        (((-L^(-(3/4:ℝ)):ℝ):ℂ)-Complex.I*(H:ℂ))
        (((1/L:ℝ):ℂ)+Complex.I*(H:ℂ)),
        ‖deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
          DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I))‖ ≤ K*L^2 := by
  obtain ⟨K,T₀,hK,hT₀,hr⟩ := marked_major_arc_character_rectangle A b hA hb
  refine ⟨K,T₀,hK,hT₀,?_⟩
  filter_upwards [hr, eventually_gt_atTop (1:ℝ)] with L hL hL1
  intro q _ hq χ x t H hx hH hHt htlo hthi
  have hLp : 0 < L := by linarith
  have hδp : 0 < L^(-(3/4:ℝ)) := Real.rpow_pos_of_pos hLp _
  have hδ1 : L^(-(3/4:ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL1 (by norm_num)
  have hσp : 0 < 1/L := one_div_pos.mpr hLp
  have hab : -L^(-(3/4:ℝ)) ≤ 1/L := by linarith
  have hab' : -L^(-(3/4:ℝ)) ≤ L⁻¹ := by simpa only [one_div] using hab
  have htpos : 0 < |t| := by linarith
  have hall : ∀ s ∈ Rectangle
      (((-L^(-(3/4:ℝ)):ℝ):ℂ)-Complex.I*(H:ℂ))
      (((1/L:ℝ):ℂ)+Complex.I*(H:ℂ)),
      DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
        DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I))‖ ≤ K*L^2 := by
    intro s hs
    have hs' : s.re ∈ Icc (-L^(-(3/4:ℝ))) (1/L) ∧ s.im ∈ Icc (-H) H := by
      simpa [Rectangle,Complex.mem_reProdIm,uIcc_of_le hab',one_div,
        uIcc_of_le (show -H ≤ H by linarith)] using hs
    have him : |s.im| ≤ H := abs_le.mpr hs'.2
    have hlow : T₀ ≤ |s.im-t| := by
      have hh := abs_sub_abs_le_abs_sub t s.im
      rw [abs_sub_comm t s.im] at hh
      linarith
    have hhigh : |s.im-t| ≤ Real.exp (b*L) := by
      calc
        _ ≤ |s.im| + |t| := abs_sub _ _
        _ ≤ 2*|t| := by linarith
        _ ≤ _ := hthi
    apply hL q hq χ (s+(1-(t:ℂ)*Complex.I))
    · simpa [sub_eq_add_neg] using hlow
    · simpa [sub_eq_add_neg] using hhigh
    · simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero]
      linarith [hs'.1.1]
    · simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero]
      linarith [hs'.1.2]
  refine ⟨?_, fun s hs => (hall s hs).2⟩
  apply marked_major_mangoldt_rectangle χ hx (by linarith) (by linarith) hσp hH
    (by linarith)
  exact fun s hs => (hall s hs).1

end ArtinMatthews
