module
public import Std.Do.Triple.Basic

@[expose] public section

namespace Std.Do

theorem Triple.of_entails_left {m} {ps : PostShape} {β: Type u} [Monad m] [WPMonad m ps]
    {P Q : Assertion ps} {R : PostCond β ps} (x : m β) (hPR : ⦃P⦄ x ⦃R⦄) (hPQ : Q ⊢ₛ P) : ⦃Q⦄ x ⦃R⦄ :=
  SPred.entails.trans hPQ hPR

theorem Triple.of_entails_right {m} {ps : PostShape} {β: Type u} [Monad m] [WPMonad m ps]
    {P : Assertion ps} {Q R : PostCond β ps} (x : m β) (hPR : ⦃P⦄ x ⦃Q⦄) (hPQ : Q ⊢ₚ R) : ⦃P⦄ x ⦃R⦄ :=
  SPred.entails.trans hPR (PredTrans.mono _ _ _ hPQ)

theorem Triple.map {m} {ps : PostShape} {α β} [Monad m] [WPMonad m ps] (f : α → β)
    (x : m α) (P : Assertion ps) (Q : PostCond β ps) :
    ⦃P⦄ (f <$> x) ⦃Q⦄ ↔ ⦃P⦄ x ⦃(fun a => Q.fst (f a), Q.snd)⦄ := by rw [Triple, WP.map]; rfl

end Std.Do
