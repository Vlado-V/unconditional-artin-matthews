module

public import ArtinMatthews.SpectralCuspEisensteinSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Actual automorphy and target-cusp reindexing, with the genuine source and
target determinant-one scaling matrices. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

def cuspEisensteinAutomorphyRow (N : ℕ) (a : SL(2,ℤ))
    (g : CongruenceSubgroup.Gamma0 N) (v : Gamma0CuspEisensteinRows N 1 a) :
    Gamma0CuspEisensteinRows N 1 a :=
  ⟨vecMul v.val (g.val:Matrix (Fin 2) (Fin 2) ℤ),by
    let M := gamma0CuspEisensteinRowRepresentative N 1 a v
    have hM : a⁻¹*M.val ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,mul_one] using M.property
    have hm : M.val*g.val ∈ gamma0CuspCorrespondence N 1 a := by
      change a⁻¹*(M.val*g.val)*1 ∈ CongruenceSubgroup.Gamma0 N
      simpa only [mul_one,mul_assoc] using (CongruenceSubgroup.Gamma0 N).mul_mem hM g.property
    refine ⟨⟨M.val*g.val,hm⟩,?_⟩
    have he : (M.val*g.val) 1=vecMul (M.val 1) (g.val:Matrix (Fin 2) (Fin 2) ℤ) := rfl
    exact he.trans (congrArg (fun v : Fin 2 → ℤ => vecMul v (g.val:Matrix (Fin 2) (Fin 2) ℤ))
      (gamma0CuspEisensteinRowRepresentative_spec N 1 a v))⟩

def cuspEisensteinAutomorphyEquiv (N : ℕ) (a : SL(2,ℤ))
    (g : CongruenceSubgroup.Gamma0 N) :
    Gamma0CuspEisensteinRows N 1 a ≃ Gamma0CuspEisensteinRows N 1 a where
  toFun := cuspEisensteinAutomorphyRow N a g
  invFun := cuspEisensteinAutomorphyRow N a g⁻¹
  left_inv v := by
    apply Subtype.ext
    change vecMul (vecMul v.val (g.val:Matrix (Fin 2) (Fin 2) ℤ))
      ((g.val⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)=v.val
    rw [vecMul_vecMul]
    change vecMul v.val ((g.val*g.val⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)=v.val
    rw [mul_inv_cancel]
    exact vecMul_one v.val
  right_inv v := by
    apply Subtype.ext
    change vecMul (vecMul v.val ((g.val⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ))
      (g.val:Matrix (Fin 2) (Fin 2) ℤ)=v.val
    rw [vecMul_vecMul]
    change vecMul v.val ((g.val⁻¹*g.val:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)=v.val
    rw [inv_mul_cancel]
    exact vecMul_one v.val

theorem cuspEisensteinRowHeight_automorphy (N : ℕ) (a : SL(2,ℤ))
    (g : CongruenceSubgroup.Gamma0 N) (v : Gamma0CuspEisensteinRows N 1 a)
    (z : UpperHalfPlane) :
    cuspEisensteinRowHeight N 1 a (cuspEisensteinAutomorphyEquiv N a g v) z =
      cuspEisensteinRowHeight N 1 a v (g.val • z) := by
  let M := gamma0CuspEisensteinRowRepresentative N 1 a v
  have he : (M.val*g.val) 1=(cuspEisensteinAutomorphyEquiv N a g v).val := by
    change vecMul (M.val 1) (g.val:Matrix (Fin 2) (Fin 2) ℤ)=
      vecMul v.val (g.val:Matrix (Fin 2) (Fin 2) ℤ)
    exact congrArg (fun v : Fin 2 → ℤ => vecMul v (g.val:Matrix (Fin 2) (Fin 2) ℤ))
      (gamma0CuspEisensteinRowRepresentative_spec N 1 a v)
  rw [cuspEisensteinRowHeight_of_row N 1 a _ (M.val*g.val) he,mul_smul]
  rfl

theorem gamma0CuspEisenstein_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisenstein N a s (g.val • z)=gamma0CuspEisenstein N a s z := by
  unfold gamma0CuspEisenstein cuspEisensteinRowSum
  congr 2
  have he := (cuspEisensteinAutomorphyEquiv N a g).tsum_eq
    (fun v : Gamma0CuspEisensteinRows N 1 a => cuspEisensteinRowTerm N 1 a s v z)
  simpa only [cuspEisensteinRowTerm,cuspEisensteinRowHeight_automorphy] using he

theorem cuspEisensteinRowHeight_reindex (N : ℕ) (r t a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinRowHeight N t a (gamma0CuspEisensteinRowReindexEquiv N r t a v) z =
      cuspEisensteinRowHeight N r a v ((r*t⁻¹ : SL(2,ℤ)) • z) := by
  let M := gamma0CuspEisensteinRowRepresentative N r a v
  have he : (M.val*r*t⁻¹ : SL(2,ℤ)) 1=
      (gamma0CuspEisensteinRowReindexEquiv N r t a v).val := by
    have hrow : (M.val*r*t⁻¹ : SL(2,ℤ)) 1=
        vecMul (M.val 1) ((r*t⁻¹ : SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_assoc]
      rfl
    exact hrow.trans (congrArg (fun v : Fin 2 → ℤ =>
      vecMul v ((r*t⁻¹ : SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ))
        (gamma0CuspEisensteinRowRepresentative_spec N r a v))
  rw [cuspEisensteinRowHeight_of_row N t a _ (M.val*r*t⁻¹) he,mul_assoc,mul_smul]
  rfl

theorem cuspEisensteinRowSum_reindex (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    cuspEisensteinRowSum N 1 a s (r⁻¹ • z)=cuspEisensteinRowSum N r a s z := by
  unfold cuspEisensteinRowSum
  congr 1
  have he := (gamma0CuspEisensteinRowReindexEquiv N 1 r a).tsum_eq
    (fun v : Gamma0CuspEisensteinRows N r a => cuspEisensteinRowTerm N r a s v z)
  simpa only [cuspEisensteinRowTerm,cuspEisensteinRowHeight_reindex,one_mul] using he

theorem gamma0CuspEisenstein_target_scaling (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisenstein N a s (gamma0TrueCuspScaling N r • z)=
      (gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowSum N r a s
        (cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
          (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z) := by
  unfold gamma0CuspEisenstein gamma0TrueCuspScaling
  rw [mul_smul,← map_inv,atkinRealMap_smul,cuspEisensteinRowSum_reindex]

end ArtinMatthews
