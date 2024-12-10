theory Anderson_mix
imports Main "../QML_var"

begin


section {* Anderson's Ontological Argument (with Mixed Quantifiers) *}

text {* Here we explore Anderson's remark, in footnote 14 of his 1990 article,
        that we ought to "take the existential quantifier in the definition of 
        necessary existence to be an [actualistic] e-quantifier [...] and so too 
        the quantifier in the conclusion of the argument. All other individual 
        quantifiers may be taken to be [possibilistic] subsistential, [...]".   *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv>  \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )" 

  axiomatization where
    A1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not>\<Phi> )) )  )\<rfloor>"  and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" and
    A4:  "\<lfloor>\<^bold>\<exists>\<Phi>.(\<^bold>\<exists>x. ((P \<Phi>) \<^bold>\<and>  (\<Phi> x) ))\<rfloor>"


subsection {* Consistency *}

  lemma True 
    nitpick [satisfy, user_axioms, expect = genuine] oops
      
      
subsection {* Existence Positive*}


subsection {* Provability of C1 *}
  
  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>x.  G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 A4 G_def)

    
subsection {* CounterSatisfiability of C1-Actualist *}
  
definition PE :: "(\<mu> \<Rightarrow> \<sigma>)  \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
  "PE  \<Phi> x \<equiv>   (\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ey.( \<Phi> y \<and> x=y)))"
  
  
corollary C2: "\<lfloor>PE G x\<rfloor>"
  nitpick [user_axioms]
  nitpick [user_axioms, satisfy] oops
  (* sledgehammer [remote_satallax remote_leo2] *)
  (*by (metis A1 A2 A3)*)
 

subsection {* Provability of A4 *}

text {* As claimed by Hájek (1996) and contrary to footnote 1 in Anderson-Gettings (1996),
        A4 is redundant. *}

  axiomatization where 
    sym: "x r y \<longrightarrow> y r x" and
    trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
    
  lemma AuxLemma1: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 sym G_def)

  theorem A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans AuxLemma1)


subsection {* Consistency (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Independence of A5 *}

text {* As claimed by Anderson-Gettings (1996) in footnote 1 and contrary to  Hájek's claim,
        A5 is not redundant. Nitpick finds a counter-model. *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv>  (\<^bold>\<forall>\<Psi>. ( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>y.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y)))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE  x \<equiv>  \<^bold>\<forall>\<Phi>. (ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  theorem A5: "\<lfloor>P NE\<rfloor>"
  nitpick [user_axioms] 
  nitpick [user_axioms, satisfy] oops


subsection {* Immunity to Modal Collapse *}  
 
text {* As claimed by Anderson, the modal collapse is not provable. 
        Nitpick finds a counter-model. *}

  theorem MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
  nitpick [user_axioms, expect = genuine]
  oops

subsection {*Positive Existence*} 
     
  axiomatization where 
    sym: "x r y \<longrightarrow> y r x" and
    trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
    
  lemma EP: "\<lfloor>P eiw\<rfloor>"
  by (metis A1 A2 A3 A4 sym trans)
    

subsection {* Counter-Satisfiability of the Main Theorem *}

text {* Unfortunately, with actualistic quantifiers only for NE and T3, 
        T3 is not provable. Nitpick finds a counter-model. *}

  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  nitpick [user_axioms] oops

  lemma PEP: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> (\<lambda>x. (\<Phi> = \<Psi>))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

  lemma PEP_Leibniz: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> \<^bold>\<forall>(\<lambda>Q. Q \<Phi> \<^bold>\<rightarrow> Q \<Psi>)) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

end
