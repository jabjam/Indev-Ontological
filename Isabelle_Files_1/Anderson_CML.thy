theory Anderson_CML
imports Main "../CFML_Lewis_var"

begin


section \<open>* Anderson's Ontological Argument -- Counterfactuals *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  
definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
            
definition NotEq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where
  "NotEq x y \<equiv> \<^bold>\<not>(x \<^bold>=\<^sup>L y)"
  
consts H :: "\<mu> \<Rightarrow> \<sigma>"
type_synonym z = " \<mu> \<Rightarrow> \<sigma>"
  
axiomatization where
    CF1: "Preorder" and
    CF2: "\<forall>w. Total(w)" and
    CF3: "LewisVC" and
    CF4: "\<forall>w. {w} = Lew_Minset w (\<^bold>\<not> \<bottom>)"

(* axiomatization where
    A1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"  and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" and
    B3:  "\<lfloor>P H\<rfloor>" *)


consts D :: "\<mu> \<Rightarrow> \<sigma>" 
  
definition DL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DL (x) \<equiv> \<^bold>\<not>(D(x))"  
    
definition Perfective1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective1 (\<phi>)  \<equiv> ( (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<box>\<rightarrow>  D(x) ) ))"  
    
definition Perfective2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective2 (\<phi>)  \<equiv>  \<^bold>\<not>( \<^bold>\<exists>\<^sup>Ex.( \<phi>(x) \<box>\<rightarrow> D(x) ))"      
  
definition Perfective ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective (\<phi>)  \<equiv> ( (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<box>\<rightarrow>  D(x) ) ))  \<^bold>\<and>    ( \<^bold>\<not>( \<^bold>\<exists>\<^sup>Ex.( \<phi>(x) \<box>\<rightarrow> D(x) )))"
    

subsection \<open>* Consistency *\<close>

(*lemma True *)
  (* nitpick [satisfy, user_axioms,card i=2,  show_all, expect = genuine, timeout =100] oops *)
      
subsection \<open>* HOL *\<close>

(*Proof found,/nitpick failed *)
theorem Pred: "\<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> x \<^bold>\<leftrightarrow>  (\<^bold>\<exists>\<^sup>Ey. (x \<^bold>=\<^sup>L y) ))\<rfloor>"
  using nonempty by blast

(*Proof found,/nitpick failed *)    
theorem Taut: " L \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
section \<open>* Perfective- satisying A1 A2 *\<close>    

(*Nitpick failed after 41 of the total and timeout 1300 *)
(* lemma A1CF: "\<lfloor>\<^bold>\<forall>\<Phi>. (((Perfective \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (Perfective (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  nitpick[user_axioms] oops *)
 

lemma A2CF2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (Perfective \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> Perfective2 \<Psi>))\<rfloor>"
  nitpick[user_axioms, card i = 3, timeout =200] oops 
    
(*Nitpick found a countermodel*)    
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  nitpick[user_axioms] oops
   

(*Section:  Perfective V2*) 

consts OP :: "\<mu> \<Rightarrow> \<sigma>"

definition DN :: "\<mu> \<Rightarrow> \<sigma>" where
  " DN (x) \<equiv> \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( OP(y)) ))(x)  )"
  
definition DNL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNL (x) \<equiv> \<^bold>\<not>(DN(x))"  
    
definition Pn1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))"  
    
definition Pn2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"      
  
definition PerfectiveV2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV2 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"


lemma PN1Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
nitpick [user_axioms, show_all] oops


lemma PN2Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
 nitpick [user_axioms] oops



end
