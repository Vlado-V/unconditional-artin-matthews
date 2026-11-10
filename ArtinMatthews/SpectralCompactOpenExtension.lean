module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A compactly supported continuous test on an open subspace extends
by zero with literal equality there and compact support in the open set. -/
noncomputable section
open Set Filter
open scoped Topology CompactlySupported
namespace ArtinMatthews

def spectralCompactOpenExtensionValue {X : Type*} [TopologicalSpace X] {U : Set X}
    (f : C_c(U,ℝ)) (x : X) : ℝ := by
  classical
  exact if hx : x∈U then f ⟨x,hx⟩ else 0

theorem spectralCompactOpenExtensionValue_apply {X : Type*} [TopologicalSpace X] {U : Set X}
    (f : C_c(U,ℝ)) (x : U) : spectralCompactOpenExtensionValue f x=f x := by
  classical
  simp only [spectralCompactOpenExtensionValue,dite_eq_left x.property,Subtype.coe_eta]

theorem spectralCompactOpenExtensionValue_zero {X : Type*} [TopologicalSpace X] {U : Set X}
    (f : C_c(U,ℝ)) {x : X} (hx : x∉U) : spectralCompactOpenExtensionValue f x=0 := by
  classical
  simp only [spectralCompactOpenExtensionValue,dite_eq_right hx]

theorem spectralCompactOpenExtensionValue_support {X : Type*} [TopologicalSpace X] {U : Set X}
    (f : C_c(U,ℝ)) :
    Function.support (spectralCompactOpenExtensionValue f)⊆Subtype.val '' tsupport f := by
  intro x hx
  by_cases hU : x∈U
  · let y : U := ⟨x,hU⟩
    have hy : f y≠0 := by
      intro h
      exact hx ((spectralCompactOpenExtensionValue_apply f y).trans h)
    exact ⟨y,subset_tsupport f hy,rfl⟩
  · exact (hx (spectralCompactOpenExtensionValue_zero f hU)).elim

theorem spectralCompactOpenExtensionValue_continuous {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U) (f : C_c(U,ℝ)) : Continuous (spectralCompactOpenExtensionValue f) := by
  let F := spectralCompactOpenExtensionValue f
  let K : Set X := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hs : Function.support F⊆K := spectralCompactOpenExtensionValue_support f
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈U
  · have hOn : ContinuousOn F U := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : U.domRestrict F = fun y : U => f y :=
        funext (spectralCompactOpenExtensionValue_apply f)
      rw [he]
      exact f.continuous
    exact hOn.continuousAt (hU.mem_nhds hx)
  · have hxK : x∉K := fun ⟨y,_,he⟩ => hx (he ▸ y.property)
    have he : F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (show x∈Kᶜ from hxK)] with y hy
      by_contra hn
      exact hy (hs hn)
    exact continuousAt_const.congr_of_eventuallyEq he

def spectralCompactOpenExtension {X : Type*} [TopologicalSpace X] [T2Space X] {U : Set X}
    (hU : IsOpen U) (f : C_c(U,ℝ)) : C_c(X,ℝ) :=
  ⟨⟨spectralCompactOpenExtensionValue f,spectralCompactOpenExtensionValue_continuous hU f⟩,
    (f.hasCompactSupport.image continuous_subtype_val).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (spectralCompactOpenExtensionValue_support f)
        (f.hasCompactSupport.image continuous_subtype_val).isClosed)⟩

theorem spectralCompactOpenExtension_tsupport {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U) (f : C_c(U,ℝ)) :
    tsupport (spectralCompactOpenExtension hU f)⊆U := by
  have h : tsupport (spectralCompactOpenExtension hU f)⊆Subtype.val '' tsupport f :=
    closure_minimal (spectralCompactOpenExtensionValue_support f)
      (f.hasCompactSupport.image continuous_subtype_val).isClosed
  intro x hx
  obtain ⟨y,_,rfl⟩ := h hx
  exact y.property

end ArtinMatthews
