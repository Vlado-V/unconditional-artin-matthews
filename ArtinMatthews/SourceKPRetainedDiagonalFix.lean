module

public import ArtinMatthews.SourceKPRetainedCloseCube
public import ArtinMatthews.SourceKPRetainedPhases
public import ArtinMatthews.SourceKPFiniteIntegralIndex


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical small diagonal lift has an actual conjugate in the
deep right level. Cubing an approximate lift removes the central
ambiguity and retains the specified canonical diagonal. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix Topology SourcePhysical
open scoped NumberField MatrixGroups AdeleRing SourcePhysical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "J" => sourceKPFiniteDeepMatrixGroup K
local notation "pr" => sourceKPFiniteAdeleProjectiveProjection K hζ
local notation "kf" => sourceKPFiniteLevelLift K hζ

theorem sourceKPRetained_diagonal_pow (u : 𝔸ᶠ[K]ˣ) (n : ℕ) :
    (D u)^n = D (u^n) := by
  induction n with
  | zero => simp only [pow_zero, sourceKPFiniteAdeleProjectiveDiagonalLift_one]
  | succ n ih =>
    rw [pow_succ, ih]
    have hphase : sourceKPAdeleMultiplier K hζ
        (sourceKPDiagonalHom 𝔸ᶠ[K] (u^n)) (sourceKPDiagonalHom 𝔸ᶠ[K] u) = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro P
      rw [sourceKPAdeleLocalMultiplier_diagonal,
        (Units.map (sourceKPAdeleEval K P).toMonoidHom).map_pow,
        (sourceFiniteKPHilbert K hζ P).map_pow, MonoidHom.pow_apply,
        sourceFiniteKPHilbert_diag, one_pow, one_pow, map_one]
    change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] (u^n)) *
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u) =
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] (u^(n+1)))
    rw [sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _ hphase,
      ← map_mul, pow_succ]

private theorem cube_mem_level_of_projection (g : Gf) (k : J) (hk : pr g = pr (kf k)) :
    g^3 ∈ Kf := by
  have hker : g*(kf k)⁻¹ ∈ (pr).ker := by
    change pr (g*(kf k)⁻¹) = 1
    rw [map_mul, map_inv, hk, mul_inv_cancel]
  rw [← sourceKPFiniteAdeleProjective_exact K hζ] at hker
  obtain ⟨z,hz⟩ := hker
  have he : g = sourceKPFiniteAdeleProjectiveCenter K hζ z * kf k := by
    rw [hz, inv_mul_cancel_right]
  have hc : (sourceKPFiniteAdeleProjectiveCenter K hζ z)^3 = 1 := by
    have hz3 : z^3 = 1 := Subtype.ext z.prop
    rw [← map_pow, hz3, map_one]
  rw [he, (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z (kf k)).mul_pow, hc, one_mul]
  exact (Kf).pow_mem ⟨k,rfl⟩ 3

variable (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "U" => sourceKPAdeleLocalUnit K P
local notation "single" => sourceKPFiniteAdditiveSingle K P

private theorem localUnit_value (u : Lˣ) :
    (U u : 𝔸ᶠ[K]) = 1 + single ((u:L)-1) := by
  apply FiniteAdeleRing.ext
  intro Q
  change (U u : 𝔸ᶠ[K]) Q = 1 + single ((u:L)-1) Q
  by_cases hQ : Q = P
  · subst Q
    have he := congrArg Units.val (sourceKPAdeleLocalUnit_same K P u)
    change (U u : 𝔸ᶠ[K]) P = (u:L) at he
    rw [he, sourceKPFiniteAdditiveSingle_same]
    ring
  · have he := congrArg Units.val (sourceKPAdeleLocalUnit_other K P u Q hQ)
    change (U u : 𝔸ᶠ[K]) Q = 1 at he
    rw [he, sourceKPFiniteAdditiveSingle_other K P ((u:L)-1) Q hQ, add_zero]

private theorem localDiagonalMatrix_continuous :
    Continuous (fun u : Lˣ => sourceKPDiagonalHom 𝔸ᶠ[K] (U u)) := by
  let f := (sourceKPDiagonalHom 𝔸ᶠ[K]).comp (sourceKPRetainedLocalUnitHom K P)
  have hv : Continuous (fun u : Lˣ => (f u : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · change Continuous (fun u : Lˣ => (U u : 𝔸ᶠ[K]))
      simp_rw [localUnit_value K P]
      exact continuous_const.add ((sourceKPFiniteAdditiveSingle_continuous K P).comp
        (Units.continuous_val.sub continuous_const))
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  change Continuous f
  apply Units.continuous_iff.mpr
  refine ⟨hv,?_⟩
  change Continuous (fun u : Lˣ =>
    (((f u)⁻¹ : GL (Fin 2) 𝔸ᶠ[K]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]))
  have he : (fun u : Lˣ => (((f u)⁻¹ : GL (Fin 2) 𝔸ᶠ[K]) :
      Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) =
      (fun u : Lˣ => (f u : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) ∘ Inv.inv := by
    funext u
    exact congrArg Units.val (f.map_inv u).symm
  rw [he]
  exact hv.comp continuous_inv

theorem sourceKPRetained_small_diagonal_level (qf : Gf) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Lˣ, ((t:L)-1) ∈ B (-(M:ℤ)) →
      (∃ w : Lˣ, w^3 = t) ∧ qf⁻¹ * D (U t) * qf ∈ Kf := by
  obtain ⟨a,ha⟩ := ProjGenLinGroup.mk_surjective (pr qf)
  let f (w : Lˣ) := a⁻¹ * sourceKPDiagonalHom 𝔸ᶠ[K] (U w) * a
  have hf : Continuous f :=
    (continuous_const.mul (localDiagonalMatrix_continuous K P)).mul continuous_const
  let V := f ⁻¹' (J : Set _)
  have hV : IsOpen V := (sourceKPFiniteDeepMatrixGroup_isOpen K).preimage hf
  have h1 : (1:Lˣ) ∈ V := by
    change a⁻¹ * sourceKPDiagonalHom 𝔸ᶠ[K] (U 1) * a ∈ J
    rw [← sourceKPRetainedLocalUnitHom_apply, map_one, map_one, mul_one, inv_mul_cancel]
    exact (J).one_mem
  let W := (Units.val : Lˣ → L) '' V
  have hW : IsOpen W := (IsOpenUnits.isOpenEmbedding_unitsVal (M := L)).isOpenMap V hV
  let E := (fun x : L => 1+x) ⁻¹' W
  have hE : IsOpen E := hW.preimage (continuous_const.add continuous_id)
  have h0 : (0:L) ∈ E := ⟨1,h1,by simp⟩
  obtain ⟨n,hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P (hE.mem_nhds h0)
  let n' := min n (-1)
  have hn' : n' < 0 := (min_le_right n (-1)).trans_lt (by omega)
  obtain ⟨M,hM,hroot⟩ := sourceKPRetained_close_cube K P n' hn'
  refine ⟨M,hM,fun t ht => ?_⟩
  obtain ⟨w,hw,hwB⟩ := hroot t ht
  refine ⟨⟨w,hw⟩,?_⟩
  have hwV : w ∈ V := by
    have hmem : (w:L)-1 ∈ B n := hwB.trans (WithZero.exp_le_exp.mpr (min_le_left _ _))
    obtain ⟨u,hu,he⟩ := hn hmem
    have huw : u = w := Units.ext (he.trans (by ring))
    exact huw ▸ hu
  let k : J := ⟨f w,hwV⟩
  have hp : pr (qf⁻¹*D (U w)*qf) = pr (kf k) := by
    rw [map_mul, map_mul, map_inv, ← ha, sourceKPFiniteAdeleProjectiveDiagonalLift_projection,
      sourceKPFiniteLevelLift_projection]
    change ProjGenLinGroup.mk a⁻¹ * ProjGenLinGroup.mk (sourceKPDiagonalHom 𝔸ᶠ[K] (U w)) *
      ProjGenLinGroup.mk a = ProjGenLinGroup.mk (a⁻¹ * sourceKPDiagonalHom 𝔸ᶠ[K] (U w) * a)
    rw [map_mul, map_mul, map_inv]
  have hc := cube_mem_level_of_projection K hζ (qf⁻¹*D (U w)*qf) k hp
  have hU : (U w)^3 = U t := by
    rw [← sourceKPRetainedLocalUnitHom_apply, ← sourceKPRetainedLocalUnitHom_apply,
      ← map_pow, hw]
  have he : (qf⁻¹*D (U w)*qf)^3 = qf⁻¹*D (U t)*qf := calc
    _ = qf⁻¹*(D (U w))^3*qf := by
      simpa only [MulAut.conj_apply, inv_inv] using
        (map_pow (MulAut.conj qf⁻¹) (D (U w)) 3).symm
    _ = _ := by rw [sourceKPRetained_diagonal_pow, hU]
  exact he ▸ hc

end
end ArtinMatthews
