module

public import ArtinMatthews.SourceKPLocalCompactProjection
public import ArtinMatthews.SourceKPAdelicCoordinateJacquetPeriod
public import ArtinMatthews.SourceKPJacquetBallCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! Both actual lifted root groups enter every finite intersection of
conjugates of the split deep level near zero. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Filter Topology SourcePhysical
open scoped NumberField MatrixGroups SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "J" => sourceKPLocalCompactDeepCoverLevel K hζ P
local notation "D" => sourceKPLocalCompactDeepBase K P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "B" => sourceLocalBall K P

attribute [local instance] sourceKPLocalProjectiveTopology

local instance sourceKPJacquetDeepConjugates_projectiveGroup : IsTopologicalGroup (PGL(2, L)) :=
  inferInstanceAs (IsTopologicalGroup (GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)))

theorem sourceKPJacquet_deepCover_cube_mem {g : G} (hg : p₀ g ∈ D) : g ^ (3 : ℕ) ∈ J := by
  rw [← sourceKPLocalCompactDeepCoverLevel_projection K hζ P] at hg
  obtain ⟨j, hj, hp⟩ := hg
  have hker : g * j⁻¹ ∈ (p₀).ker := by
    change p₀ (g * j⁻¹) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rw [← sourceFiniteKP2Projective_exact K hζ P] at hker
  obtain ⟨z, hz⟩ := hker
  have he : g = z₀ z * j := by rw [hz, inv_mul_cancel_right]
  have hz3 : z ^ (3 : ℕ) = 1 := Subtype.ext z.property
  rw [he, (sourceFiniteKP2ProjectiveCenter_commute K hζ P z j).mul_pow,
    ← map_pow, hz3, map_one, one_mul]
  exact (J).pow_mem hj 3

private theorem sourceKPJacquet_deepLift_cube {a : GL (Fin 2) L}
    (ha : a ∈ Set.range (sourceKPDeepLocalBase K P)) :
    (l₀ a) ^ (3 : ℕ) = l₀ (a ^ (3 : ℕ)) := by
  obtain ⟨d, rfl⟩ := ha
  let j := sourceKPLocalCompactDeepLift K hζ P
  let C := sourceKPLocalCompactCover K hζ P
  have h := map_pow ((C).subtype.comp j) d (3 : ℕ)
  change l₀ (sourceKPDeepLocalBase K P (d ^ (3 : ℕ))) =
    (l₀ (sourceKPDeepLocalBase K P d)) ^ (3 : ℕ) at h
  rw [map_pow] at h
  exact h.symm

private theorem sourceKPJacquet_upperMatrix_continuous :
    Continuous (sourceGL2Upper : L → GL (Fin 2) L) := by
  have hv : Continuous (fun t : L => (sourceGL2Upper t : Matrix (Fin 2) (Fin 2) L)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  have hi (t : L) : (sourceGL2Upper t)⁻¹ = sourceGL2Upper (-t) := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    rw [sourceGL2Upper_mul, neg_add_cancel, sourceGL2Upper_zero]
  have hvneg : Continuous (fun t : L => (sourceGL2Upper (-t) : Matrix (Fin 2) (Fin 2) L)) :=
    hv.comp continuous_neg
  exact Units.continuous_iff.mpr ⟨hv, by simpa only [hi] using hvneg⟩

private theorem sourceKPJacquet_lowerMatrix_eq_weyl (t : L) :
    sourceGL2Lower t = sourceGL2Weyl * sourceGL2Upper t * sourceGL2Weyl := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Lower, sourceGL2Upper, sourceGL2Weyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sourceKPJacquet_upperMatrix_cube (t : L) :
    (sourceGL2Upper t) ^ (3 : ℕ) = sourceGL2Upper (3 * t) := by
  rw [pow_succ, pow_two, sourceGL2Upper_mul, sourceGL2Upper_mul]
  congr 1
  ring

private theorem sourceKPJacquet_lowerMatrix_cube (t : L) :
    (sourceGL2Lower t) ^ (3 : ℕ) = sourceGL2Lower (3 * t) := by
  have hw : (sourceGL2Weyl : GL (Fin 2) L)⁻¹ = sourceGL2Weyl := by
    symm
    exact eq_inv_iff_mul_eq_one.mpr sourceGL2Weyl_square
  have h := map_pow (MulAut.conj (sourceGL2Weyl : GL (Fin 2) L)) (sourceGL2Upper t) (3 : ℕ)
  simpa only [MulAut.conj_apply, hw, sourceKPJacquet_upperMatrix_cube,
    sourceKPJacquet_lowerMatrix_eq_weyl K P] using h.symm

private theorem sourceKPJacquet_conjugate_lift_eventually_deep
    (a : L → GL (Fin 2) L) (ha : Continuous a) (ha0 : a 0 = 1)
    (ha3 : ∀ t, a t ^ (3 : ℕ) = a (3 * t)) (g : G) :
    ∀ᶠ t : L in 𝓝 0, g⁻¹ * l₀ (a t) * g ∈ J := by
  have hAt : Tendsto a (𝓝 0) (𝓝 1) := by simpa only [ha0] using ha.tendsto 0
  have hbase : ∀ᶠ t : L in 𝓝 0, a t ∈ Set.range (sourceKPDeepLocalBase K P) :=
    hAt.eventually ((sourceKPDeepLocalBase_range_isOpen K P).mem_nhds ⟨1, map_one _⟩)
  let q (t : L) : PGL(2, L) := (p₀ g)⁻¹ * ProjGenLinGroup.mk (a t) * p₀ g
  have hq : Continuous q :=
    (continuous_const.mul ((sourceKPLocalProjective_mk_continuous K P).comp ha)).mul continuous_const
  have hq0 : q 0 = 1 := by simp only [q, ha0, map_one, mul_one, inv_mul_cancel]
  have hqAt : Tendsto q (𝓝 0) (𝓝 1) := by simpa only [hq0] using hq.tendsto 0
  have hproj : ∀ᶠ t : L in 𝓝 0, q t ∈ D :=
    hqAt.eventually ((sourceKPLocalCompactDeepBase_isOpen K P).mem_nhds (D).one_mem)
  have h3 : ∀ᶠ t : L in 𝓝 0, g⁻¹ * l₀ (a (3 * t)) * g ∈ J := by
    filter_upwards [hbase, hproj] with t ht hqt
    have hp : p₀ (g⁻¹ * l₀ (a t) * g) ∈ D := by
      rw [map_mul, map_mul, map_inv]
      exact hqt
    have h := sourceKPJacquet_deepCover_cube_mem K hζ P hp
    have hl : (l₀ (a t)) ^ (3 : ℕ) = l₀ (a (3 * t)) :=
      (sourceKPJacquet_deepLift_cube K hζ P ht).trans (congrArg l₀ (ha3 t))
    have hc := map_pow (MulAut.conj g⁻¹) (l₀ (a t)) (3 : ℕ)
    have he : (g⁻¹ * l₀ (a t) * g) ^ (3 : ℕ) = g⁻¹ * l₀ (a (3 * t)) * g := by
      simpa only [MulAut.conj_apply, inv_inv, hl] using hc.symm
    rwa [he] at h
  have hthird : Tendsto (fun t : L => t / 3) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : L => t / 3) := continuous_id.div_const _
    simpa only [zero_div] using hc.tendsto (0 : L)
  filter_upwards [hthird.eventually h3] with t ht
  have he : (3 : L) * (t / 3) = t := by field_simp
  simpa only [he] using ht

theorem sourceKPJacquet_conjugate_roots_eventually_deep (g : G) :
    ∀ᶠ t : L in 𝓝 0,
      g⁻¹ * l₀ (sourceGL2Upper t) * g ∈ J ∧ g⁻¹ * l₀ (sourceGL2Lower t) * g ∈ J := by
  have hUpper := sourceKPJacquet_upperMatrix_continuous K P
  have hLower : Continuous (sourceGL2Lower : L → GL (Fin 2) L) := by
    have hW : Continuous (fun _ : L => (sourceGL2Weyl : GL (Fin 2) L)) := continuous_const
    have hc : Continuous (fun t : L => sourceGL2Weyl * sourceGL2Upper t * sourceGL2Weyl) :=
      (hW.mul hUpper).mul hW
    change Continuous (fun t : L => sourceGL2Lower t)
    simpa only [sourceKPJacquet_lowerMatrix_eq_weyl K P] using hc
  have hLower0 : sourceGL2Lower (0 : L) = 1 := by
    rw [sourceKPJacquet_lowerMatrix_eq_weyl K P, sourceGL2Upper_zero, mul_one, sourceGL2Weyl_square]
  exact (sourceKPJacquet_conjugate_lift_eventually_deep K hζ P _ hUpper
    sourceGL2Upper_zero (sourceKPJacquet_upperMatrix_cube K P) g).and
    (sourceKPJacquet_conjugate_lift_eventually_deep K hζ P _ hLower
      hLower0 (sourceKPJacquet_lowerMatrix_cube K P) g)

theorem sourceKPJacquet_conjugate_roots_deep_ball (F : Finset G) :
    ∃ M : ℕ, ∀ t ∈ B (-(M : ℤ)), ∀ g ∈ F,
      g⁻¹ * l₀ (sourceGL2Upper t) * g ∈ J ∧ g⁻¹ * l₀ (sourceGL2Lower t) * g ∈ J := by
  have h : ∀ᶠ t : L in 𝓝 0, ∀ g : ↥F,
      g.val⁻¹ * l₀ (sourceGL2Upper t) * g.val ∈ J ∧
        g.val⁻¹ * l₀ (sourceGL2Lower t) * g.val ∈ J :=
    Filter.eventually_all.mpr fun g => sourceKPJacquet_conjugate_roots_eventually_deep K hζ P g.val
  obtain ⟨n, hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P h
  let M := (-n).toNat
  have hM : -(M : ℤ) ≤ n := by dsimp only [M]; omega
  refine ⟨M, fun t ht g hg => hn ?_ ⟨g, hg⟩⟩
  exact sourceKPJacquetSelfDual_ball_mono K P hM ht

end
end ArtinMatthews
