Theorem po_with_one:
∀A. po A one ≅ A
Proof
cheat
QED

Theorem tp_eq:
∀f g. f∶ A×B → C ∧ g∶ A×B → C ⇒ (tp f = tp f' ⇔ f = f')
Proof
cheat
QED

Theorem tp_to_p:
 ⇒ tp f = fb
Proof
 
Theorem is_tp:
∀A B X f h. f∶ A×X → B ∧ h∶ X → exp A B ∧
            (ev A B) o ⟨p1 A X, h o (p2 A X)⟩ = f ⇒
            h = tp f
Proof
metis_tac[ax2]
QED

(*‘⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ =
   ⟨p1 A N, (tp f) o (p2 A N)⟩ o ⟨p1 A N, s o (p2 A N)⟩’*)        
Theorem pcompose: (*decompose coposition of arrows lemma*)
Proof


Theorem ev eq ⇒ arrow eq:

Proof

Theorem to_p_eq:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
Proof
cheat
QED                   


Theorem to_p_eq:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ∧
         (p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇒ f = g
Proof
cheat
QED                   
                      
Theorem iterated_p_eq:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              (f = g ⇔
              (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
              (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
              (p2 (A×B) C) o f = (p2 (A×B) C) o g)
Proof
cheat
QED

Theorem iterated_p_eq_applied:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              ((p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
               (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
               (p2 (A×B) C) o f = (p2 (A×B) C) o g ⇒ f = g)
Proof
cheat
QED
