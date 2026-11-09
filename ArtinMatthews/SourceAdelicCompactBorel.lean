module

public import ArtinMatthews.SourceAdelicIwasawa


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar and diagonal coordinates of the actual compact–Borel intersection. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

theorem sourceKPRingProjectiveBorel_matrix_factor {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (hg : ProjGenLinGroup.mk g ∈ sourceKPRingBorel R) :
    ∃ (x : R) (a u : Rˣ),
      g = (sourceKPUpperMatrix R x * sourceKPDiagonalHom R a) * GeneralLinearGroup.scalar (Fin 2) u ∧
      g 1 0 = 0 ∧ g 1 1 = (u : R) ∧ g 0 0 = (a : R) * (u : R) ∧ g 0 1 = x * (u : R) := by
  obtain ⟨b, hb, hbg⟩ := hg
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hbg
  refine ⟨b 0 1, GeneralLinearGroup.det b, u, ?_, ?_, ?_, ?_, ?_⟩
  · exact hu.symm.trans (congrArg (fun c : GL (Fin 2) R => c * GeneralLinearGroup.scalar (Fin 2) u)
      (sourceKPRingNormalizedBorel_factor R b hb))
  · rw [← hu, sourceKPMatrix_right_scalar_entry, hb.1, zero_mul]
  · rw [← hu, sourceKPMatrix_right_scalar_entry, hb.2, one_mul]
  · rw [← hu, sourceKPMatrix_right_scalar_entry]
    congr 1
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hb.1, hb.2]
    simp
  · rw [← hu, sourceKPMatrix_right_scalar_entry]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactBorel_factor (g : GL (Fin 2) 𝔸[K])
    (hg : g ∈ SourceKPAdelicBaseCompactMatrix K hζ)
    (hb : ProjGenLinGroup.mk g ∈ sourceKPRingBorel 𝔸[K]) :
    ∃ (x : 𝔸[K]) (a u : 𝔸[K]ˣ),
      g = (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a) *
        GeneralLinearGroup.scalar (Fin 2) u ∧
      g 1 0 = 0 ∧ g 1 1 = (u : 𝔸[K]) ∧
      g 0 0 = (a : 𝔸[K]) * (u : 𝔸[K]) ∧ g 0 1 = x * (u : 𝔸[K]) ∧
      (∀ P : HeightOneSpectrum (𝓞 K),
        sourceKPFiniteVal K P ((u : 𝔸[K]).2 P) = 1 ∧
        sourceKPFiniteVal K P ((a : 𝔸[K]).2 P) = 1 ∧
        (a : 𝔸[K]).2 P = sourceKPAdelicBaseFiniteAt K P g 0 0 /
          sourceKPAdelicBaseFiniteAt K P g 1 1) ∧
      (∀ v : InfinitePlace K,
        ‖sourceKPArchComplexEquiv K hζ v ((u : 𝔸[K]).1 v)‖ = 1 ∧
        ‖sourceKPArchComplexEquiv K hζ v ((a : 𝔸[K]).1 v)‖ = 1 ∧
        sourceKPArchComplexEquiv K hζ v ((a : 𝔸[K]).1 v) =
          sourceKPAdelicBaseComplexAt K hζ v g 0 0 / sourceKPAdelicBaseComplexAt K hζ v g 1 1) := by
  obtain ⟨x, a, u, hfactor, h10, h11, h00, h01⟩ := sourceKPRingProjectiveBorel_matrix_factor g hb
  refine ⟨x, a, u, hfactor, h10, h11, h00, h01, ?_, ?_⟩
  · intro P
    let G := sourceKPAdelicBaseFiniteAt K P g
    let A := (a : 𝔸[K]).2 P
    let U := (u : 𝔸[K]).2 P
    have hG : SourceKPIntegralMatrix (sourceKPFiniteVal K P) G := hg.1 P
    have hG10 : G 1 0 = 0 := congrArg (fun t : 𝔸[K] => t.2 P) h10
    have hG11 : G 1 1 = U := congrArg (fun t : 𝔸[K] => t.2 P) h11
    have hG00 : G 0 0 = A * U := congrArg (fun t : 𝔸[K] => t.2 P) h00
    have hU : sourceKPFiniteVal K P U = 1 := by
      have h := sourceKPIntegralMatrix_bottom_unit (sourceKPFiniteVal K P) hG
      simpa only [hG10, hG11, map_zero, zero_ne_one, false_or] using h
    have hdet : (GeneralLinearGroup.det G : P.adicCompletion K) = A * U ^ 2 := by
      rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hG10, hG11, hG00]
      ring
    have hA : sourceKPFiniteVal K P A = 1 := by
      simpa only [hdet, map_mul, map_pow, hU, one_pow, mul_one] using hG.det_unit
    refine ⟨hU, hA, ?_⟩
    change A = G 0 0 / G 1 1
    rw [hG11]
    apply (eq_div_iff (show U ≠ 0 from fun h => by simp [h] at hU)).mpr
    exact hG00.symm
  · intro v
    let G := sourceKPAdelicBaseComplexAt K hζ v g
    let e := sourceKPArchComplexEquiv K hζ v
    let A := e ((a : 𝔸[K]).1 v)
    let U := e ((u : 𝔸[K]).1 v)
    obtain ⟨k, hk⟩ := hg.2 v
    change sourceArchUnitaryGL k = G at hk
    have hG10 : G 1 0 = 0 := by
      have h := congrArg (fun t : 𝔸[K] => e (t.1 v)) h10
      change e ((g 1 0).1 v) = e (0 : v.Completion) at h
      rw [map_zero] at h
      exact h
    have hG11 : G 1 1 = U := congrArg (fun t : 𝔸[K] => e (t.1 v)) h11
    have hG00 : G 0 0 = A * U := by
      have h := congrArg (fun t : 𝔸[K] => e (t.1 v)) h00
      change e ((g 0 0).1 v) = e ((a : 𝔸[K]).1 v * (u : 𝔸[K]).1 v) at h
      rw [map_mul] at h
      exact h
    have hbottom : sourceArchBottomNorm G = 1 := by
      rw [← hk]
      simpa [sourceArchBottomNorm] using sourceArchBottomNorm_unitary 1 k
    have hU : ‖U‖ = 1 := by
      have hsq : ‖U‖ ^ 2 = 1 := by
        simpa only [sourceArchBottomNorm, hG10, hG11, norm_zero, zero_pow (by decide : 2 ≠ 0),
          zero_add] using hbottom
      nlinarith [norm_nonneg U]
    have hdet : (GeneralLinearGroup.det G : ℂ) = A * U ^ 2 := by
      rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hG10, hG11, hG00]
      ring
    have hA : ‖A‖ = 1 := by
      have hn : ‖(GeneralLinearGroup.det G : ℂ)‖ = 1 := by
        rw [← hk]
        exact sourceArchUnitaryGL_det_norm k
      simpa only [hdet, norm_mul, norm_pow, hU, one_pow, mul_one] using hn
    refine ⟨hU, hA, ?_⟩
    change A = G 0 0 / G 1 1
    rw [hG11]
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [hU]; norm_num))).mpr
    exact hG00.symm

end
end ArtinMatthews
