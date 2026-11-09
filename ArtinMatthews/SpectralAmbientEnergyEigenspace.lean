module

public import ArtinMatthews.SpectralAmbientSpectralAtoms
public import ArtinMatthews.SpectralGamma0CuspidalProjection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Stone atom is the orthogonal projection onto the full
energy eigenspace. The cusp and noncuspidal components both remain in
that same eigenspace. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0AmbientEnergyEigenspace (N : ℕ) [NeZero N] (l : ℝ) : Submodule ℂ (Gamma0RegionL2 N) :=
  (gamma0Green N-(((l+1)⁻¹:ℝ):ℂ) • ContinuousLinearMap.id ℂ (Gamma0RegionL2 N)).ker

theorem mem_gamma0AmbientEnergyEigenspace_iff (N : ℕ) [NeZero N] (l : ℝ) (v : Gamma0RegionL2 N) :
    v∈gamma0AmbientEnergyEigenspace N l ↔ gamma0Green N v=(((l+1)⁻¹:ℝ):ℂ) • v := by
  rw [gamma0AmbientEnergyEigenspace,LinearMap.mem_ker]
  change gamma0Green N v-(((l+1)⁻¹:ℝ):ℂ) • v=0 ↔ _
  exact sub_eq_zero

theorem gamma0AmbientEnergyEigenspace_closed (N : ℕ) [NeZero N] (l : ℝ) :
    IsClosed (gamma0AmbientEnergyEigenspace N l : Set (Gamma0RegionL2 N)) :=
  ContinuousLinearMap.isClosed_ker _

instance gamma0AmbientEnergyEigenspace_complete (N : ℕ) [NeZero N] (l : ℝ) :
    CompleteSpace (gamma0AmbientEnergyEigenspace N l) :=
  (gamma0AmbientEnergyEigenspace_closed N l).isComplete.completeSpace_coe

theorem gamma0AmbientSpectralAtomVector_eq_projection (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) :
    gamma0AmbientSpectralAtomVector N u l=(gamma0AmbientEnergyEigenspace N l).starProjection u := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((mem_gamma0AmbientEnergyEigenspace_iff N l _).mpr (gamma0AmbientSpectralAtomVector_green N u l))
  intro w hw
  exact inner_eq_zero_symm.mpr (gamma0AmbientSpectralAtomVector_orthogonal N u w l
    ((mem_gamma0AmbientEnergyEigenspace_iff N l w).mp hw))

theorem gamma0AmbientEnergyEigenspace_of_pencil (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (v : gamma0EnergySpace N) (hv : gamma0EnergyResolventPencil N (l:ℂ) v=0) :
    gamma0EnergyInclusion N v∈gamma0AmbientEnergyEigenspace N l := by
  let J := gamma0EnergyInclusion N
  let a : ℂ := ((l+1:ℝ):ℂ)
  have ha : a≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hV : v=a • gamma0EnergyMassAdjoint N (J v) := by
    change v-((l:ℂ)+1) • gamma0EnergyMassAdjoint N (J v)=0 at hv
    simpa only [a,Complex.ofReal_add,Complex.ofReal_one] using sub_eq_zero.mp hv
  apply (mem_gamma0AmbientEnergyEigenspace_iff N l (J v)).mpr
  change J (gamma0EnergyMassAdjoint N (J v))=(((l+1)⁻¹:ℝ):ℂ) • J v
  rw [Complex.ofReal_inv]
  change J (gamma0EnergyMassAdjoint N (J v))=a⁻¹ • J v
  have hw := congrArg J hV
  rw [map_smul] at hw
  calc
    _ = a⁻¹ • (a • J (gamma0EnergyMassAdjoint N (J v))) := by
      rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
    _ = _ := congrArg (fun x : Gamma0RegionL2 N => a⁻¹ • x) hw.symm

theorem gamma0AmbientEnergyEigenspace_energy_pencil (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (m : Gamma0RegionL2 N) (hm : m∈gamma0AmbientEnergyEigenspace N l) :
    ∃ v : gamma0EnergySpace N,gamma0EnergyInclusion N v=m ∧ gamma0EnergyResolventPencil N (l:ℂ) v=0 := by
  have h := gamma0AmbientSpectralAtomVector_energy_pencil N m l hl
  rw [gamma0AmbientSpectralAtomVector_eq_projection N m l,Submodule.starProjection_eq_self_iff.mpr hm] at h
  exact h

theorem gamma0AmbientEnergyEigenspace_orthogonal_of_ne (N : ℕ) [NeZero N]
    {l k : ℝ} (hne : l≠k)
    {v w : Gamma0RegionL2 N} (hv : v∈gamma0AmbientEnergyEigenspace N l)
    (hw : w∈gamma0AmbientEnergyEigenspace N k) : inner ℂ v w=0 := by
  let a : ℝ := (l+1)⁻¹
  let b : ℝ := (k+1)⁻¹
  have ha : (a:ℂ)≠(b:ℂ) := by
    intro h
    have h' : a=b := Complex.ofReal_injective h
    apply hne
    exact add_right_cancel (inv_injective h')
  have hV : gamma0Green N v=(a:ℂ) • v := (mem_gamma0AmbientEnergyEigenspace_iff N l v).mp hv
  have hW : gamma0Green N w=(b:ℂ) • w := (mem_gamma0AmbientEnergyEigenspace_iff N k w).mp hw
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0Green_selfAdjoint N)) v w
  change inner ℂ (gamma0Green N v) w=inner ℂ v (gamma0Green N w) at hsym
  rw [hV,hW,inner_smul_left,inner_smul_right,Complex.conj_ofReal] at hsym
  have hz : ((a:ℂ)-(b:ℂ))*inner ℂ v w=0 := by rw [sub_mul,hsym,sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem gamma0CuspidalProjection_ambient_eigen (N : ℕ) [NeZero N]
    (l : ℝ) (m : Gamma0RegionL2 N) (hm : m∈gamma0AmbientEnergyEigenspace N l) :
    (gamma0CuspidalProjection N m).val∈gamma0AmbientEnergyEigenspace N l := by
  let p := gamma0CuspidalProjection N m
  let a : ℂ := (((l+1)⁻¹:ℝ):ℂ)
  let Q := gamma0AllHeightCuspidalMassSpace N
  have hm' : gamma0Green N m=a • m := (mem_gamma0AmbientEnergyEigenspace_iff N l m).mp hm
  have hq : gamma0Green N p.val∈Q := gamma0Green_mem_allHeightCuspidalMassSpace N _ p.property
  have hD : gamma0Green N p.val-a • p.val∈Q := Q.sub_mem hq (Q.smul_mem _ p.property)
  have hOrth (w : Q) : inner ℂ (gamma0Green N p.val-a • p.val) w.val=0 := by
    let wG : Q := ⟨gamma0Green N w.val,gamma0Green_mem_allHeightCuspidalMassSpace N _ w.property⟩
    have h1 := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0Green_selfAdjoint N)) p.val w.val
    have h2 := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0Green_selfAdjoint N)) m w.val
    change inner ℂ (gamma0Green N p.val) w.val=inner ℂ p.val wG.val at h1
    change inner ℂ (gamma0Green N m) w.val=inner ℂ m wG.val at h2
    have hp (v : Q) : inner ℂ p.val v.val=inner ℂ m v.val := gamma0CuspidalProjection_inner_right N m v
    rw [inner_sub_left,h1,hp wG,← h2,hm',inner_smul_left,inner_smul_left,hp w,sub_self]
  have hzero := inner_self_eq_zero.mp (hOrth ⟨_,hD⟩)
  exact (mem_gamma0AmbientEnergyEigenspace_iff N l _).mpr (sub_eq_zero.mp hzero)

theorem gamma0NoncuspidalRemainder_ambient_eigen (N : ℕ) [NeZero N]
    (l : ℝ) (m : Gamma0RegionL2 N) (hm : m∈gamma0AmbientEnergyEigenspace N l) :
    gamma0NoncuspidalRemainder N m∈gamma0AmbientEnergyEigenspace N l := by
  change m-(gamma0CuspidalProjection N m).val∈gamma0AmbientEnergyEigenspace N l
  exact (gamma0AmbientEnergyEigenspace N l).sub_mem hm (gamma0CuspidalProjection_ambient_eigen N l m hm)

theorem gamma0FullCuspidalSpectralBasis_mem_ambient_eigenspace (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasis N i).val∈
      gamma0AmbientEnergyEigenspace N (gamma0AllHeightGradientSpectralValue N i) := by
  apply (mem_gamma0AmbientEnergyEigenspace_iff N _ _).mpr
  rw [gamma0FullCuspidalSpectralBasis_eigen,gamma0AllHeightGradientSpectralValue,sub_add_cancel,inv_inv,
    gamma0AllHeightSpectralValue_real]

end ArtinMatthews
