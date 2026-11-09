module

public import ArtinMatthews.GiantSignedTraceProjection


set_option backward.privateInPublic true
@[expose] public section

/-! A projected trace is finite whenever each row has finitely many
moves ending in the allowed states. The underlying trace remains unchanged. -/
namespace ArtinMatthews
noncomputable section

universe u v
variable {X : Type u}

theorem giantSignedTraceWithin_finite (good : X → Prop)
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, ∀ x, Finite {m : r.Move x // good (r.target x m)}) (x : X) :
    Finite {t : GiantSignedTrace rs x // GiantSignedTraceWithin good rs x t} := by
  induction rs generalizing x with
  | nil =>
      change Finite {t : PUnit.{v+1} // True}
      infer_instance
  | cons r rs ih =>
      let U := {m : r.Move x // good (r.target x m)}
      let T (m : U) := {t : GiantSignedTrace rs (r.target x m.val) //
        GiantSignedTraceWithin good rs (r.target x m.val) t}
      letI : Finite U := hr r List.mem_cons_self x
      letI : ∀ m : U, Finite (T m) := fun m =>
        ih (fun a ha => hr a (List.mem_cons_of_mem _ ha)) (r.target x m.val)
      let encode (t : {t : GiantSignedTrace (r::rs) x // GiantSignedTraceWithin good (r::rs) x t}) :
          Σ m : U, T m :=
        ⟨⟨t.1.1, t.2.2.1⟩, ⟨t.1.2, t.2.2.2⟩⟩
      apply Finite.of_injective encode
      intro s t h
      apply Subtype.ext
      exact congrArg (fun z : Σ m : U, T m => (⟨z.1.1, z.2.1⟩ : GiantSignedTrace (r::rs) x)) h

end
end ArtinMatthews
