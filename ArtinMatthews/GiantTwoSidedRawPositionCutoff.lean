module

public import ArtinMatthews.GiantTwoSidedRawSharedAggregation


set_option backward.privateInPublic true
@[expose] public section

/-! The cutoff acts on the true quotient position, independently of the
size of the copied product. The two original physical boxes are finite
and cover every surviving pair of quotient positions. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedSharedProductMax {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : ℕ) : ℕ :=
  (univ : Finset (MarkedPhysicalMarking P k)).sup markedPhysicalMarkingProduct

def giantTwoSidedRawPositionBox {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k N : ℕ) : Finset ℕ := Ioc 0 (giantTwoSidedSharedProductMax P k*N)

theorem giantTwoSidedRawPositionBox_cover {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {k N : ℕ}
    (c : MarkedPhysicalMarking P k) (w : ↥(Ioc 0 N)) :
    markedPhysicalMarkingProduct c*w.val ∈ giantTwoSidedRawPositionBox P k N ∧
      markedPhysicalMarkingProduct c*(w.val+1) ∈ giantTwoSidedRawPositionBox P k (N+1) := by
  have hc := markedPhysicalMarkingProduct_pos hP c
  have hle : markedPhysicalMarkingProduct c ≤ giantTwoSidedSharedProductMax P k :=
    Finset.le_sup (f:=markedPhysicalMarkingProduct) (mem_univ c)
  have hw := mem_Ioc.mp w.property
  exact ⟨mem_Ioc.mpr ⟨Nat.mul_pos hc hw.1,Nat.mul_le_mul hle hw.2⟩,
    mem_Ioc.mpr ⟨Nat.mul_pos hc (Nat.succ_pos _),Nat.mul_le_mul hle (Nat.succ_le_succ hw.2)⟩⟩

def giantTwoSidedRawSharedCapEmb {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k N N' : ℕ} {Z Z' : Finset ℕ} (hle : N ≤ N') :
    GiantTwoSidedRawSharedEdge P k N Z Z' ↪ GiantTwoSidedRawSharedEdge P k N' Z Z' where
  toFun a := ⟨(a.val.1,⟨a.val.2.1.val,mem_Ioc.mpr
    ⟨(mem_Ioc.mp a.val.2.1.property).1,(mem_Ioc.mp a.val.2.1.property).2.trans hle⟩⟩,
    a.val.2.2),a.property⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d : GiantTwoSidedRawSharedEdge P k N' Z Z' => d.val.1) hab
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun d : GiantTwoSidedRawSharedEdge P k N' Z Z' => d.val.2.1.val) hab)
      · exact congrArg (fun d : GiantTwoSidedRawSharedEdge P k N' Z Z' => d.val.2.2) hab

theorem giantTwoSidedRawShared_sum_eq_of_cutoff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m N N' : ℕ} {Z Z' : Finset ℕ} (hle : N ≤ N')
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (hcut : ∀ w : ℕ,N<w → Ψ ((w:ℝ)/x)=0) :
    (∑ a : GiantTwoSidedRawSharedEdge P k N' Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a) =
      ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a := by
  classical
  let E : GiantTwoSidedRawSharedEdge P k N Z Z' ↪ GiantTwoSidedRawSharedEdge P k N' Z Z' :=
    giantTwoSidedRawSharedCapEmb hle
  let s := (univ : Finset (GiantTwoSidedRawSharedEdge P k N Z Z')).map E
  let f := giantTwoSidedRawSharedTerm (P:=P) (k:=k) (N:=N') (Z:=Z) (Z':=Z') x q Ψ χ F G
  have hs : (∑ a ∈ s,f a) = ∑ a : GiantTwoSidedRawSharedEdge P k N' Z Z',f a := by
    apply sum_subset (subset_univ _)
    intro a _ ha
    have hw : N<a.val.2.1.val := by
      by_contra! hw
      let b : GiantTwoSidedRawSharedEdge P k N Z Z' :=
        ⟨(a.val.1,⟨a.val.2.1.val,mem_Ioc.mpr ⟨(mem_Ioc.mp a.val.2.1.property).1,hw⟩⟩,
          a.val.2.2),a.property⟩
      exact ha (mem_map.mpr ⟨b,mem_univ _,rfl⟩)
    simp only [f,giantTwoSidedRawSharedTerm,hcut _ hw,zero_div,mul_zero,zero_mul]
  rw [← hs,show s = univ.map E from rfl,sum_map]
  rfl

theorem giantTwoSidedRawPositionKernel_cutoff {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (Φ : ℝ → ℝ) (hΦ : ∀ t,T<t → Φ t=0) (w : ℕ) (hw : ⌊T*x⌋₊<w) :
    (((w:ℝ)/x*Φ ((w:ℝ)/x):ℝ):ℂ)=0 := by
  have h := (Nat.floor_lt (mul_nonneg hT hx.le)).mp hw
  rw [hΦ _ ((lt_div_iff₀ hx).mpr h),mul_zero,Complex.ofReal_zero]

end
end ArtinMatthews
