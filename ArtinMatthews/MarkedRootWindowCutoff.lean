module

public import ArtinMatthews.MarkedRootStateWindow
public import ArtinMatthews.MarkedRawStateInclude


set_option backward.privateInPublic true
@[expose] public section

/-! The actual physical root endpoint test is the zero extension of the
literal full first/beta-good cutoff on its finite box window. The chosen
primitive completions and every active and pending coordinate agree. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x d₀ Y U V : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

include hZ in
theorem markedRootStateWindow_primitive (p : ℝ × (ℝ × ℝ)) :
    ∀ z∈markedRootStateWindow Z U V p,IsCoprime z.1 z.2 :=
  fun z hz => hZ z (markedRootStateWindow_subset Z U V p hz)

theorem markedRootMemoryEndpointTest_eq_zero_of_outside (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (hs : s.1.1∉markedRootStateWindow Z U V p) :
    markedRootMemoryEndpointTest e x d₀ Y U V hZ p s=0 := by
  have hb : ¬MarkedRootPhysicalBox U V (markedRootIntegerVector s.1.1) p :=
    fun hb => hs (Finset.mem_filter.mpr ⟨s.1.2,hb⟩)
  simp only [markedRootMemoryEndpointTest,MarkedRootMemoryEndpointGood,hb,false_and,and_false,ite_false]

set_option backward.isDefEq.respectTransparency false in
theorem markedRootMemoryEndpointTest_window (p : ℝ × (ℝ × ℝ))
    (hp : p∈markedRootBoxDomain)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B (markedRootStateWindow Z U V p)) :
    markedRootMemoryEndpointTest e x d₀ Y U V hZ p
      (markedRawStateInclude (markedRootStateWindow_subset Z U V p) s)=
      markedRawDirtyGoodCutoff e x p.1 d₀ Y
        (fun z => markedPrimitiveCoordinateCompletion z.1
          (markedRootStateWindow_primitive U V hZ p _ z.2)) (fun _ => 1) s := by
  have hb := (Finset.mem_filter.mp s.1.2).2
  rw [markedRawDirtyGoodCutoff_eq_ite]
  unfold markedRootMemoryEndpointTest MarkedRootMemoryEndpointGood markedRawStateInclude
  simp only [hp,hb,true_and]
  rfl

end ArtinMatthews
