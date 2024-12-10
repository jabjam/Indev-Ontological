theory Anderson_CML_2nd
imports Main "../CFML_Lewis_var2"

begin


section \<open>* Taylor's Ontological Argument -- Counterfactuals *\<close>

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
    CF3: "LewisVC"


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

lemma PerfConj : "\<lfloor>Perfective(\<phi>) \<^bold>\<leftrightarrow>  (Perfective1(\<phi>)  \<^bold>\<and> Perfective2(\<phi>))\<rfloor> "
  apply (metis Perfective_def Perfective1_def Perfective2_def)
  prf
  done

subsection \<open>* Consistency *\<close>

(*Proof found *)
lemma True 
  nitpick [satisfy, user_axioms, card i=2, expect = genuine] oops 
      
subsection \<open>* HOL *\<close>

(*Proof found,/nitpick failed *)
theorem Pred: "\<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> x \<^bold>\<leftrightarrow>  (\<^bold>\<exists>\<^sup>Ey. (x \<^bold>=\<^sup>L y) ))\<rfloor>"
  using nonempty by blast

(*Proof found,/nitpick failed *)    
theorem Taut: " True \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
section \<open>* Perfective- satisying A1 A2 *\<close>    


(*Vampire found a proof- using Perfective_def nonempty by presburger *)
lemma A1CF: "\<lfloor>\<^bold>\<forall>\<Phi>. (((Perfective \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (Perfective (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  using Perfective1_def Perfective2_def PerfConj CF1 CF2 CF3 by metis

(*proof -
  have "sK0 \<^bold>\<Turnstile> mexistsB eiw"
    by (simp add: nonempty)
  then have "(\<exists>m. sK0 \<^bold>\<Turnstile> (Perfective sK1 \<^bold>\<and> eiw m)) \<or> \<lfloor>\<lambda>i. \<forall>p. i \<^bold>\<Turnstile> Perfective p \<longrightarrow> i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective (\<lambda>m i. i \<^bold>\<Turnstile> (\<^sup>\<not>p) m))\<rfloor>"
    by metis (* > 1.0 s, timed out *)
  moreover
  { assume "\<exists>m. sK0 \<^bold>\<Turnstile> (Perfective sK1 \<^bold>\<and> eiw m)"
    then have ?thesis
      by (smt (z3) Perfective_def) (* > 1.0 s, timed out *) }
  ultimately show ?thesis
    by argo
qed *)


axiomatization where CF4: "\<forall>w. {w} = Lew_Minset w (\<^bold>\<not> \<bottom>)"

lemma A2CF1: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (Perfective \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> Perfective1 \<Psi>))\<rfloor>"
  proof -
  
  (* By LewisVC we know *)
  have case_split: "\<forall>w. (\<^bold>\<not>\<phi> \<box>\<rightarrow> \<bottom>)(w) \<longleftrightarrow> 
     (( \<not>( \<exists>v\<in>Ww(w). \<^bold>\<not>\<phi> v)  ) \<or> KMin(\<^bold>\<not>\<phi>)(\<bottom>)(w))"
    using CF3 by auto
  
  (* From here we see we need to use the preorder properties *)
  have preorder: "\<forall>w. reflexive(w) \<and> transitive(w)"
    using Preorder by auto

  (* And we know the order is total *)
  have total: "\<forall>w. Total(w)"
    using totale by auto
	
    have p1_def: "Perfective1(\<Phi>) \<equiv> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<Phi>(x))) \<box>\<rightarrow> D(x) ))"
    by (simp add: Perfective1_def)
   
  fix w
     assume perf_Phi: "Perfective(\<Phi>) w" 
     assume strict_impl: "\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<Psi> x)) w"
     
  (* By our assumption perf_phi, consider any c that exists in w *)
  fix c
  assume "eiw c w"	
	
  (* Case 1: Empty intersection case *)
  {
    assume case1: "\<forall>v. v\<in>Ww(w) \<longrightarrow> (v \<^bold>\<Turnstile> (\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<Psi> x)))"
    
    (* For our arbitrary c that exists in w *)
    assume p1_holds: "(\<^bold>\<not>(\<Phi>(c)) \<box>\<rightarrow> D(c))(w)"
        (* using Perfective1_def perf_Phi `eiw c w` by metis *)

    (* By similar case analysis on this counterfactual *)
    have "(\<forall>x. ((\<^bold>\<not>(\<Phi>(c)) x \<and> r(w)(x, x)) \<longleftrightarrow> \<not>(r(w)(x, x)))) \<or>
          KMin(\<^bold>\<not>(\<Phi>(c)))(D(c))(w)"
      using LVC p1_holds Preorder by metis

    (* Subcases for phi *)
    {
      (* Subcase 1: When [[\<not>ϕ(c)]] \<inter> Ww = \<emptyset> *)
      assume subcase1: "\<forall>v. v\<in>Ww(w) \<longrightarrow> \<not>(v \<^bold>\<Turnstile> \<^bold>\<not>(\<Phi>(c)))"
      
      (* This means ϕ(c) holds in all accessible worlds *)
      have "\<forall>v.  v\<in>Ww(w) \<longrightarrow> (v \<^bold>\<Turnstile> \<Phi>(c))"
        using subcase1 by auto

      (* By our strict implication assumption *)
      assume "\<forall>v.  v\<in>Ww(w) \<longrightarrow> (v \<^bold>\<Turnstile> \<Psi>(c))"
        (* using strict_impl `eiw c w` by metis *)

      (* Therefore [[\<not>\<psi>(c)]] \<inter> Ww = \<emptyset> *)
      have "(\<^bold>\<not>(\<Psi>(c)) \<box>\<rightarrow> D(c))(w)"
        using CF1 LVC by auto
    }
    {
      (* Subcase 2: The existential case *)
      assume subcase2: "\<exists>v. r(w)(v)(v) \<and> (v \<^bold>\<Turnstile> \<^bold>\<not>(\<Phi>(c))) \<and>
                       (\<forall>u. r(w)(u)(v) \<longrightarrow> (u \<^bold>\<Turnstile> (\<^bold>\<not>(\<Phi>(c)) \<^bold>\<rightarrow> D(c))))"

      obtain v where v_props:
        "r(w)(v)(v)"
        "v \<^bold>\<Turnstile> \<^bold>\<not>(\<Phi>(c))"
        "\<forall>u. r(w)(u)(v) \<longrightarrow> (u \<^bold>\<Turnstile> (\<^bold>\<not>(\<Phi>(c)) \<^bold>\<rightarrow> D(c)))"
        using subcase2 by auto

      (* Need to show this implies the counterfactual for \<psi> *)
      have "(\<^bold>\<not>(\<Psi>(c)) \<box>\<rightarrow> D(c))(w)"
        using LVC
	proof (cases "\<exists>v. (r w v v) \<and> (v  \<^bold>\<Turnstile>  \<^bold>\<not>(\<Psi>(c)))")
  		case False
  	then show ?thesis using LVC by metis
	next
  		case True
  	then obtain v where v_def: "r w v v" "v  \<^bold>\<Turnstile>  \<^bold>\<not>(\<Psi>(c))" by auto
  
  	(* For any u \<le>w v *)
  {
    fix u
    assume u_prop: "r w u v"
    
    have "u  \<^bold>\<Turnstile>  \<^bold>\<not>(\<Phi>(c))"
      using strict_impl u_prop v_def by auto
      
    hence "u  \<^bold>\<Turnstile>  D(c)"
      using v_props u_prop by auto
  }
  
  then show ?thesis using LVC v_def by auto
qed
    }

    (* By cases on phi, we get the result for \<psi> *)
    have "(\<^bold>\<not>(\<Psi>(c)) \<box>\<rightarrow> D(c))(w)"
  	using LewisVC subcase1 subcase2 by auto
  }

  (* Case 2: The contradiction case *)
  {
    assume case2: "KMin(\<^bold>\<not>(\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<psi> x)))(\<bottom>)(w)"
    
    (* This means there exists a v where: *)
    obtain v where v_props: 
      "r(w)(v)(v)" 
      "v \<^bold>\<Turnstile> \<^bold>\<not>(\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<psi> x))"
      "\<forall>u. r(w)(u)(v) \<longrightarrow> (u \<^bold>\<Turnstile> (\<^bold>\<not>(\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<psi> x)) \<^bold>\<rightarrow> \<bottom>))"
      using case2 by (auto simp add: Lew_Minset_def)

    (* By reflexivity *)
    have "r(w)(v)(v)" using CF1 by auto
    
    (* This leads to contradiction *)
    have "v \<^bold>\<Turnstile> \<bottom>"
      using v_props `r(w)(v)(v)` by auto
      
    have "False" using `v \<^bold>\<Turnstile> \<bottom>` by auto
  }

  (* By cases, we must have Case 1 *)
  hence "\<forall>v. r(w)(v)(v) \<longrightarrow> (v \<^bold>\<Turnstile> (\<^bold>\<forall>\<^sup>Ex. (\<Phi> x \<^bold>\<rightarrow> \<psi> x)))"
    using case_split  by auto
  
  show ?thesis sorry
qed


lemma A2CF2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (Perfective \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>   \<^bold>\<not>(\<^bold>\<box>(  \<^bold>\<not>(Perfective2 \<Psi>) ))) )\<rfloor>"
  using Perfective_def Perfective2_def CF1 CF2 CF3 CF4 by metis

lemma A2CF23: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (Perfective \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>  (Perfective2 \<Psi>)) )\<rfloor>"
  using Perfective_def Perfective2_def CF1 CF2 CF3 CF4 by metis

        
lemma Giv2: "\<lfloor>Perfective2 DL\<rfloor>"
  using Perfective2_def DL_def CF3 CF1 by blast

lemma Giv1: "\<lfloor>Perfective1 DL\<rfloor>"
  using Perfective1_def DL_def CF3 CF1 by metis


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
