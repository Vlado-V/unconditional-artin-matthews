module

public import ArtinMatthews.SpectralEisensteinMixedUpperEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The literal high modes of the compact upper truncations at the chosen
forcing cutoff. Both truncated energy remainders have zero high means. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspUpperEnergyCombination_mode (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (q : ℂ) (A : ℝ) (hA : 0<A) (Y : ℝ) (hY : 0<Y)
    (hw : (gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)≤Y)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0CuspConstantTerm N (gamma0EisensteinCuspClassRepresentative N i) Y hY
      (gamma0EnergyInclusion N (gamma0CuspUpperEnergyCombination N q A hA c))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
        fun y => c i*eisensteinOutgoingApprox q A
          (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)) := by
  let r := gamma0EisensteinCuspClassRepresentative N
  let C := gamma0CuspConstantTerm N (r i) Y hY
  let J := gamma0EnergyInclusion N
  let W (j : Gamma0EisensteinCuspClasses N) := gamma0CuspUpperTruncatedEnergy N (r j) q A hA
  have hDiag (j : Gamma0EisensteinCuspClasses N) :
      C (J (W j))=if i=j then C (J (W i)) else 0 := by
    by_cases hij : i=j
    · subst j
      simp
    · rw [ite_eq_right hij]
      have hm := gamma0CuspUpperTruncatedEnergy_constant_mode N (r i) (r j) q A hA Y hY hw
      have hI : gamma0CuspEisensteinIndicator N (r i) (r j)=0 := by
        rw [gamma0CuspEisensteinIndicator_eq_cuspClass]
        simp only [r,gamma0EisensteinCuspClassRepresentative_class,ite_eq_right hij]
      simp only [hI,zero_mul] at hm
      exact Lp.ext (hm.trans (Lp.coeFn_zero ℂ 2 _).symm)
  have hsum : C (J (gamma0CuspUpperEnergyCombination N q A hA c))=c i • C (J (W i)) := by
    change C (J (∑ j,c j • W j))=_
    simp only [map_sum,map_smul]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hDiag j,ite_eq_right hj.symm,smul_zero]
    · simp
  have hI : gamma0CuspEisensteinIndicator N (r i) (r i)=1 := by
    simp [gamma0CuspEisensteinIndicator_eq_cuspClass]
  have hm := gamma0CuspUpperTruncatedEnergy_constant_mode N (r i) (r i) q A hA Y hY hw
  simp only [hI,one_mul] at hm
  change C (J (gamma0CuspUpperEnergyCombination N q A hA c)) =ᵐ[_] _
  rw [hsum]
  filter_upwards [Lp.coeFn_smul (c i) (C (J (W i))),hm] with y hy hmy
  rw [hy,Pi.smul_apply,hmy,smul_eq_mul]

theorem gamma0CompactForcingUpperEnergy_mode (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (i : Gamma0EisensteinCuspClasses N) (s : ℂ) (A : ℝ) (hA : 0<A) :
    let r := gamma0EisensteinCuspClassRepresentative N i
    gamma0CuspConstantTerm N r Y.height Y.pos
      (gamma0EnergyInclusion N (gamma0CompactForcingUpperEnergy N ψ Y s A hA))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y.height]
        fun y => gamma0CompactForcingMatchedCoefficient N ψ Y s i*eisensteinOutgoingApprox (1-s) A
          (y/(gamma0CuspTrueWidth N r:ℝ)) := by
  dsimp only
  let r := gamma0EisensteinCuspClassRepresentative N i
  have hW : (gamma0CuspTrueWidth N r:ℝ)≤Y.height := by
    have h := Y.high r
    have hp : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
    linarith
  have hz := (gamma0TruncatedFormData_mem_iff_cusp_representatives N Y.height Y.pos _).mp
    (gamma0CompactForcingMatchedEnergy_mem N ψ Y s) i
  rw [gamma0CompactForcingUpperEnergy,map_add,map_add,hz,zero_add]
  exact gamma0CuspUpperEnergyCombination_mode N i (1-s) A hA Y.height Y.pos hW
    (gamma0CompactForcingMatchedCoefficient N ψ Y s)

theorem gamma0EisensteinUpperCombination_mode (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (s : ℂ) (A : ℝ) (hA : 0<A)
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    let r := gamma0EisensteinCuspClassRepresentative N i
    gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N (gamma0EisensteinUpperCombination N s A hA c))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
        fun y => eisensteinCriticalTruncatedPair s A (c i) ((gamma0CuspScatteringMatrix N s).mulVec c i)
          (y/(gamma0CuspTrueWidth N r:ℝ)) := by
  dsimp only
  let r := gamma0EisensteinCuspClassRepresentative N i
  let C := gamma0CuspConstantTerm N r Y hY
  let J := gamma0EnergyInclusion N
  let b := (gamma0CuspScatteringMatrix N s).mulVec c
  let U := C (J (gamma0CuspUpperEnergyCombination N s A hA c))
  let V := C (J (gamma0CuspUpperEnergyCombination N (1-s) A hA b))
  have hW := (gamma0EisensteinMatchingHeight_width_le N r).trans hmin
  have hSub : gamma0EisensteinCriticalBaseEnergy N s c∈(gamma0TruncatedFormData N Y hY).subspace :=
    (gamma0TruncatedFormData N Y hY).subspace.sum_mem (fun j _ =>
      (gamma0TruncatedFormData N Y hY).subspace.smul_mem _
        (gamma0CuspEisensteinMatchedTruncatedEnergy_mem_atHeight N Y hY hmin _ s))
  have hz := (gamma0TruncatedFormData_mem_iff_cusp_representatives N Y hY _).mp hSub i
  rw [gamma0EisensteinUpperCombination,map_add,map_add,map_add,map_add,hz,zero_add]
  have hU := gamma0CuspUpperEnergyCombination_mode N i s A hA Y hY hW c
  have hV := gamma0CuspUpperEnergyCombination_mode N i (1-s) A hA Y hY hW b
  filter_upwards [Lp.coeFn_add U V,hU,hV] with y hy hu hv
  change (U+V) y=_
  rw [hy,Pi.add_apply,hu,hv]
  rfl

end ArtinMatthews
