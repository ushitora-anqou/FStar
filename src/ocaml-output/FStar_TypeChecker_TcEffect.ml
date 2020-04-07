open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun eff_name  ->
      fun comb  ->
        fun n1  ->
          fun uu____58  ->
            match uu____58 with
            | (us,t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t  in
                (match uu____80 with
                 | (us1,t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1
                          in
                       match uu____98 with
                       | (t2,lc,g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                        in
                     (match uu____93 with
                      | (t2,ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2
                             in
                          (match uu____122 with
                           | (g_us,t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty
                                  in
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length
                                          in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int
                                        in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3)
                                        in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156
                                      in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____165 ->
                                        let uu____166 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1  ->
                                                  fun u2  ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2
                                                       in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us)
                                           in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1
                                                  in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us
                                                  in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186)
                                              in
                                           FStar_Errors.raise_error uu____180
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
  
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun reason  ->
        fun r  ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____229 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid
                 in
              FStar_All.pipe_right uu____229 FStar_Util.must  in
            let uu____234 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts  in
            match uu____234 with
            | (uu____239,pure_wp_t) ->
                let uu____241 =
                  let uu____242 =
                    FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                  [uu____242]  in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____241 r
             in
          let uu____275 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t
             in
          match uu____275 with
          | (pure_wp_uvar,uu____293,guard_wp) -> (pure_wp_uvar, guard_wp)
  
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        (let uu____328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____328
         then
           let uu____333 = FStar_Syntax_Print.term_to_string t  in
           let uu____335 =
             match k with
             | FStar_Pervasives_Native.None  -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1
              in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____333 uu____335
         else ());
        (let env1 =
           let uu___54_344 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_344.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_344.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_344.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_344.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_344.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_344.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_344.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_344.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_344.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_344.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_344.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_344.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_344.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_344.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_344.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_344.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_344.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_344.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_344.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_344.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_344.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_344.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_344.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_344.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_344.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_344.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_344.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_344.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_344.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_344.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_344.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_344.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_344.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_344.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_344.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_344.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_344.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_344.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_344.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___54_344.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_344.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_344.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_344.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_344.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_344.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_344.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         match k with
         | FStar_Pervasives_Native.None  ->
             let uu____346 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t
                in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____352 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k1  in
             ())
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____374 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____374
         then
           let uu____379 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____379
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____397 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____397)
        else ();
        (let log_combinator s uu____426 =
           match uu____426 with
           | (us,t,ty) ->
               let uu____455 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____455
               then
                 let uu____460 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____466 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____460
                   uu____466
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____491 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____491
             (fun uu____508  ->
                match uu____508 with
                | (t,u) ->
                    let uu____519 =
                      let uu____520 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____520
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____519, u))
            in
         let fresh_x_a x a =
           let uu____534 =
             let uu____535 =
               let uu____536 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____536 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____535
              in
           FStar_All.pipe_right uu____534 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           check_and_gen env0 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
            in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____588 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____588 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____612 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____612 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____632 = fresh_a_and_u_a "a"  in
                    (match uu____632 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____653 =
                             let uu____654 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____654
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____653
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____685 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____685  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____690 =
                             let uu____693 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____693
                              in
                           (sig_us, uu____690, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____702 =
            let repr_ts =
              let uu____724 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____724 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____752 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____752 with
            | (repr_us,repr_t,repr_ty) ->
                let underlying_effect_lid =
                  let repr_t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.UnfoldUntil
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_zero);
                      FStar_TypeChecker_Env.AllowUnboundUniverses] env0
                      repr_t
                     in
                  let uu____783 =
                    let uu____784 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____784.FStar_Syntax_Syntax.n  in
                  match uu____783 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____787,t,uu____789) ->
                      let uu____814 =
                        let uu____815 = FStar_Syntax_Subst.compress t  in
                        uu____815.FStar_Syntax_Syntax.n  in
                      (match uu____814 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____818,c) ->
                           let uu____840 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____840
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____843 ->
                           let uu____844 =
                             let uu____850 =
                               let uu____852 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____855 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____852 uu____855
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____850)
                              in
                           FStar_Errors.raise_error uu____844 r)
                  | uu____859 ->
                      let uu____860 =
                        let uu____866 =
                          let uu____868 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____871 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____868 uu____871
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____866)  in
                      FStar_Errors.raise_error uu____860 r
                   in
                ((let uu____876 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____882 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____882)
                     in
                  if uu____876
                  then
                    let uu____885 =
                      let uu____891 =
                        let uu____893 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____896 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____893 uu____896
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____891)
                       in
                    FStar_Errors.raise_error uu____885 r
                  else ());
                 (let uu____903 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____903 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____927 = fresh_a_and_u_a "a"  in
                      (match uu____927 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____953 = signature  in
                               match uu____953 with
                               | (us1,t,uu____968) -> (us1, t)  in
                             let uu____985 =
                               let uu____986 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____986
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____985
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1013 =
                               let uu____1016 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1016
                                 (fun uu____1029  ->
                                    match uu____1029 with
                                    | (t,u1) ->
                                        let uu____1036 =
                                          let uu____1039 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1039
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1036)
                                in
                             FStar_Syntax_Util.arrow bs uu____1013  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1042 =
                               let uu____1055 =
                                 let uu____1058 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1058
                                  in
                               (repr_us, repr_t, uu____1055)  in
                             (uu____1042, underlying_effect_lid))))))
             in
          match uu____702 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1131 = signature  in
                    match uu____1131 with | (us,t,uu____1146) -> (us, t)  in
                  let repr_ts =
                    let uu____1164 = repr  in
                    match uu____1164 with | (us,t,uu____1179) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1229 =
                    let uu____1235 =
                      let uu____1237 = FStar_Util.string_of_int n1  in
                      let uu____1239 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1241 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1237 uu____1239 uu____1241
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1235)  in
                  FStar_Errors.raise_error uu____1229 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1271 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1271 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1299 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1299 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1323 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1323 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1344 = fresh_a_and_u_a "a"  in
                             match uu____1344 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1375 =
                                     let uu____1376 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1376.FStar_Syntax_Syntax.n  in
                                   match uu____1375 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1388) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1416 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1416 with
                                        | (a',uu____1426)::(x',uu____1428)::bs1
                                            ->
                                            let uu____1458 =
                                              let uu____1459 =
                                                let uu____1464 =
                                                  let uu____1467 =
                                                    let uu____1468 =
                                                      let uu____1475 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1475)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1468
                                                     in
                                                  [uu____1467]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1464
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1459
                                               in
                                            let uu____1482 =
                                              let uu____1495 =
                                                let uu____1498 =
                                                  let uu____1499 =
                                                    let uu____1506 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1506)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1499
                                                   in
                                                [uu____1498]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1495
                                               in
                                            FStar_All.pipe_right uu____1458
                                              uu____1482)
                                   | uu____1521 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1545 =
                                   let uu____1550 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1551 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1550 u_a uu____1551  in
                                 (match uu____1545 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1571 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1571
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1576 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1576);
                                       (let uu____1577 =
                                          let uu____1580 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1580
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1577)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1609 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1609 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1621 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1621 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1645 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1645 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1666 = fresh_a_and_u_a "a"  in
                              match uu____1666 with
                              | (a,u_a) ->
                                  let uu____1686 = fresh_a_and_u_a "b"  in
                                  (match uu____1686 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1715 =
                                           let uu____1716 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1716.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1715 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1728) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1756 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1756 with
                                              | (a',uu____1766)::(b',uu____1768)::bs1
                                                  ->
                                                  let uu____1798 =
                                                    let uu____1799 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1799
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1897 =
                                                    let uu____1910 =
                                                      let uu____1913 =
                                                        let uu____1914 =
                                                          let uu____1921 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1921)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1914
                                                         in
                                                      let uu____1928 =
                                                        let uu____1931 =
                                                          let uu____1932 =
                                                            let uu____1939 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1939)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1932
                                                           in
                                                        [uu____1931]  in
                                                      uu____1913 ::
                                                        uu____1928
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1910
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1798 uu____1897)
                                         | uu____1954 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1978 =
                                         let uu____1989 =
                                           let uu____1994 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1995 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1994 u_a
                                             uu____1995
                                            in
                                         match uu____1989 with
                                         | (repr1,g) ->
                                             let uu____2010 =
                                               let uu____2017 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2017
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2010, g)
                                          in
                                       (match uu____1978 with
                                        | (f,guard_f) ->
                                            let uu____2057 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2070 =
                                                let uu____2075 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2094 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2075 u_b
                                                  uu____2094
                                                 in
                                              match uu____2070 with
                                              | (repr1,g) ->
                                                  let uu____2109 =
                                                    let uu____2116 =
                                                      let uu____2117 =
                                                        let uu____2118 =
                                                          let uu____2121 =
                                                            let uu____2124 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2124
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2121
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2118
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2117
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2116
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2109, g)
                                               in
                                            (match uu____2057 with
                                             | (g,guard_g) ->
                                                 let uu____2176 =
                                                   let uu____2181 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2182 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2181
                                                     u_b uu____2182
                                                    in
                                                 (match uu____2176 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2199 =
                                                        let uu____2204 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2205 =
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                           in
                                                        pure_wp_uvar
                                                          uu____2204 repr1
                                                          uu____2205 r
                                                         in
                                                      (match uu____2199 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2225 =
                                                               let uu____2228
                                                                 =
                                                                 let uu____2229
                                                                   =
                                                                   let uu____2230
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2230]
                                                                    in
                                                                 let uu____2231
                                                                   =
                                                                   let uu____2242
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2242]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2229;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2231;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2228
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2225
                                                              in
                                                           let guard_eq =
                                                             FStar_TypeChecker_Rel.teq
                                                               env ty k
                                                              in
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env)
                                                              [guard_f;
                                                              guard_g;
                                                              guard_repr;
                                                              g_pure_wp_uvar;
                                                              guard_eq];
                                                            (let uu____2301 =
                                                               let uu____2304
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2304
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2301)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2333 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2333 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2361 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2361 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2386 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2386
                          then
                            let uu____2391 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2397 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2391 uu____2397
                          else ());
                         (let uu____2406 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2406 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2427 = fresh_a_and_u_a "a"  in
                                match uu____2427 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2456 =
                                        let uu____2457 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2457.FStar_Syntax_Syntax.n  in
                                      match uu____2456 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2469) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2497 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2497 with
                                           | (a',uu____2507)::bs1 ->
                                               let uu____2527 =
                                                 let uu____2528 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2528
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2594 =
                                                 let uu____2607 =
                                                   let uu____2610 =
                                                     let uu____2611 =
                                                       let uu____2618 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2618)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2611
                                                      in
                                                   [uu____2610]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2607
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2527 uu____2594)
                                      | uu____2633 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2651 =
                                      let uu____2662 =
                                        let uu____2667 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2668 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2667 u uu____2668
                                         in
                                      match uu____2662 with
                                      | (repr1,g) ->
                                          let uu____2683 =
                                            let uu____2690 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2690
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2683, g)
                                       in
                                    (match uu____2651 with
                                     | (f,guard_f) ->
                                         let uu____2730 =
                                           let uu____2735 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2736 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2735 u
                                             uu____2736
                                            in
                                         (match uu____2730 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2753 =
                                                let uu____2758 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2759 =
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   in
                                                pure_wp_uvar uu____2758 ret_t
                                                  uu____2759 r
                                                 in
                                              (match uu____2753 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2777 =
                                                       let uu____2778 =
                                                         let uu____2779 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2779]  in
                                                       let uu____2780 =
                                                         let uu____2791 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2791]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2778;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2780;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2777
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2846 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2846
                                                     then
                                                       let uu____2851 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2851
                                                     else ());
                                                    (let guard_eq =
                                                       FStar_TypeChecker_Rel.teq
                                                         env ty k
                                                        in
                                                     FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env)
                                                       [guard_f;
                                                       guard_ret_t;
                                                       guard_wp;
                                                       guard_eq];
                                                     (let uu____2858 =
                                                        let uu____2861 =
                                                          let uu____2862 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2862
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2861
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2858)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2893 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2893 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2909 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2909 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2933 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2933 with
                          | (us,t) ->
                              let uu____2952 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2952 with
                               | (uu____2969,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2973 = fresh_a_and_u_a "a"  in
                                     match uu____2973 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3002 =
                                             let uu____3003 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3003.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3002 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3015) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3043 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3043 with
                                                | (a',uu____3053)::bs1 ->
                                                    let uu____3073 =
                                                      let uu____3074 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3074
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3172 =
                                                      let uu____3185 =
                                                        let uu____3188 =
                                                          let uu____3189 =
                                                            let uu____3196 =
                                                              let uu____3199
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3199
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3196)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3189
                                                           in
                                                        [uu____3188]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3185
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3073 uu____3172)
                                           | uu____3220 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3238 =
                                           let uu____3249 =
                                             let uu____3254 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3255 =
                                               let uu____3256 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3256
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3254 u_a
                                               uu____3255
                                              in
                                           match uu____3249 with
                                           | (repr1,g) ->
                                               let uu____3277 =
                                                 let uu____3284 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3284
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3277, g)
                                            in
                                         (match uu____3238 with
                                          | (f_bs,guard_f) ->
                                              let uu____3324 =
                                                let uu____3335 =
                                                  let uu____3340 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3341 =
                                                    let uu____3342 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3342
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3340 u_a
                                                    uu____3341
                                                   in
                                                match uu____3335 with
                                                | (repr1,g) ->
                                                    let uu____3363 =
                                                      let uu____3370 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3370
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3363, g)
                                                 in
                                              (match uu____3324 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3417 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3417
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3425 =
                                                     let uu____3430 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3449 =
                                                       let uu____3450 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3450
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3430
                                                       u_a uu____3449
                                                      in
                                                   (match uu____3425 with
                                                    | (t_body,guard_body) ->
                                                        let k =
                                                          FStar_Syntax_Util.abs
                                                            (FStar_List.append
                                                               bs
                                                               [f_bs;
                                                               g_bs;
                                                               p_b]) t_body
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let guard_eq =
                                                          FStar_TypeChecker_Rel.teq
                                                            env t k
                                                           in
                                                        (FStar_All.pipe_right
                                                           [guard_f;
                                                           guard_g;
                                                           guard_body;
                                                           guard_eq]
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env));
                                                         (let uu____3510 =
                                                            let uu____3513 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3513
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3510,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3526 =
                        let uu____3529 =
                          let uu____3538 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3538 FStar_Util.must  in
                        FStar_All.pipe_right uu____3529
                          FStar_Pervasives_Native.snd
                         in
                      uu____3526.FStar_Syntax_Syntax.pos  in
                    let uu____3567 = if_then_else1  in
                    match uu____3567 with
                    | (ite_us,ite_t,uu____3582) ->
                        let uu____3595 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3595 with
                         | (us,ite_t1) ->
                             let uu____3602 =
                               let uu____3613 =
                                 let uu____3614 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3614.FStar_Syntax_Syntax.n  in
                               match uu____3613 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3628,uu____3629) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3655 =
                                     let uu____3662 =
                                       let uu____3665 =
                                         let uu____3668 =
                                           let uu____3677 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3677
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3668
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3665
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3662
                                       (fun l  ->
                                          let uu____3821 = l  in
                                          match uu____3821 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3655 with
                                    | (f,g,p) ->
                                        let uu____3846 =
                                          let uu____3847 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3847 bs1
                                           in
                                        let uu____3848 =
                                          let uu____3849 =
                                            let uu____3850 =
                                              let uu____3853 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst)
                                                 in
                                              FStar_All.pipe_right uu____3853
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.bv_to_name)
                                               in
                                            FStar_All.pipe_right uu____3850
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg)
                                             in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            ite_t1 uu____3849 r
                                           in
                                        (uu____3846, uu____3848, f, g, p))
                               | uu____3880 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3602 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3897 =
                                    let uu____3906 = stronger_repr  in
                                    match uu____3906 with
                                    | (uu____3927,subcomp_t,subcomp_ty) ->
                                        let uu____3942 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3942 with
                                         | (uu____3955,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3966 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3966 with
                                               | (uu____3979,subcomp_ty1) ->
                                                   let uu____3981 =
                                                     let uu____3982 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3982.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3981 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3994) ->
                                                        let uu____4015 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4015
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4121 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4137 =
                                                 let uu____4138 =
                                                   let uu____4141 =
                                                     FStar_All.pipe_right
                                                       bs_except_last
                                                       (FStar_List.map
                                                          (fun uu____4161  ->
                                                             FStar_Syntax_Syntax.tun))
                                                      in
                                                   FStar_List.append
                                                     uu____4141 [t]
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____4138
                                                   (FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg)
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 subcomp_t1 uu____4137 r
                                                in
                                             let uu____4170 = aux f_t  in
                                             let uu____4173 = aux g_t  in
                                             (uu____4170, uu____4173))
                                     in
                                  (match uu____3897 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4190 =
                                         let aux t =
                                           let uu____4207 =
                                             let uu____4208 =
                                               let uu____4235 =
                                                 let uu____4252 =
                                                   let uu____4261 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       ite_t_applied
                                                      in
                                                   FStar_Util.Inr uu____4261
                                                    in
                                                 (uu____4252,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               (t, uu____4235,
                                                 FStar_Pervasives_Native.None)
                                                in
                                             FStar_Syntax_Syntax.Tm_ascribed
                                               uu____4208
                                              in
                                           FStar_Syntax_Syntax.mk uu____4207
                                             r
                                            in
                                         let uu____4302 = aux subcomp_f  in
                                         let uu____4303 = aux subcomp_g  in
                                         (uu____4302, uu____4303)  in
                                       (match uu____4190 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4307 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4307
                                              then
                                                let uu____4312 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4314 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4312 uu____4314
                                              else ());
                                             (let uu____4319 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4319 with
                                              | (uu____4326,uu____4327,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4330 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4330 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4332 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4332 with
                                                    | (uu____4339,uu____4340,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4344 =
                                                              let uu____4345
                                                                =
                                                                FStar_Syntax_Syntax.lid_as_fv
                                                                  FStar_Parser_Const.not_lid
                                                                  FStar_Syntax_Syntax.delta_constant
                                                                  FStar_Pervasives_Native.None
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____4345
                                                                FStar_Syntax_Syntax.fv_to_tm
                                                               in
                                                            let uu____4346 =
                                                              let uu____4347
                                                                =
                                                                FStar_All.pipe_right
                                                                  p_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____4347]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              uu____4344
                                                              uu____4346 r
                                                             in
                                                          let uu____4380 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4380 g_g
                                                           in
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env g_g1)))))))));
                   (let tc_action env act =
                      let env01 = env  in
                      let r =
                        (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                         in
                      if
                        (FStar_List.length
                           act.FStar_Syntax_Syntax.action_params)
                          <> Prims.int_zero
                      then
                        (let uu____4404 =
                           let uu____4410 =
                             let uu____4412 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4412
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4410)
                            in
                         FStar_Errors.raise_error uu____4404 r)
                      else ();
                      (let uu____4419 =
                         let uu____4424 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4424 with
                         | (usubst,us) ->
                             let uu____4447 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4448 =
                               let uu___446_4449 = act  in
                               let uu____4450 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4451 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___446_4449.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___446_4449.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___446_4449.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4450;
                                 FStar_Syntax_Syntax.action_typ = uu____4451
                               }  in
                             (uu____4447, uu____4448)
                          in
                       match uu____4419 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4455 =
                               let uu____4456 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4456.FStar_Syntax_Syntax.n  in
                             match uu____4455 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4482 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4482
                                 then
                                   let repr_ts =
                                     let uu____4486 = repr  in
                                     match uu____4486 with
                                     | (us,t,uu____4501) -> (us, t)  in
                                   let repr1 =
                                     let uu____4519 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4519
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4529 =
                                       let uu____4530 =
                                         FStar_Syntax_Syntax.as_arg
                                           ct.FStar_Syntax_Syntax.result_typ
                                          in
                                       uu____4530 ::
                                         (ct.FStar_Syntax_Syntax.effect_args)
                                        in
                                     FStar_Syntax_Syntax.mk_Tm_app repr1
                                       uu____4529 r
                                      in
                                   let c1 =
                                     let uu____4548 =
                                       let uu____4551 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4551
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4548
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4554 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4555 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4555 with
                            | (act_typ1,uu____4563,g_t) ->
                                let uu____4565 =
                                  let uu____4572 =
                                    let uu___471_4573 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___471_4573.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___471_4573.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___471_4573.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___471_4573.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___471_4573.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___471_4573.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___471_4573.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___471_4573.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___471_4573.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___471_4573.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___471_4573.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___471_4573.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___471_4573.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___471_4573.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___471_4573.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___471_4573.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___471_4573.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___471_4573.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___471_4573.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___471_4573.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___471_4573.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___471_4573.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___471_4573.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___471_4573.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___471_4573.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___471_4573.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___471_4573.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___471_4573.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___471_4573.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___471_4573.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___471_4573.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___471_4573.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___471_4573.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___471_4573.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___471_4573.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___471_4573.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___471_4573.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___471_4573.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___471_4573.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___471_4573.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___471_4573.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___471_4573.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___471_4573.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___471_4573.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___471_4573.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___471_4573.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4572
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4565 with
                                 | (act_defn,uu____4576,g_d) ->
                                     ((let uu____4579 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4579
                                       then
                                         let uu____4584 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4586 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4584 uu____4586
                                       else ());
                                      (let uu____4591 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4599 =
                                           let uu____4600 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4600.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4599 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4610) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4633 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4633 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4649 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4649 with
                                                   | (a_tm,uu____4669,g_tm)
                                                       ->
                                                       let uu____4683 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4683 with
                                                        | (repr1,g) ->
                                                            let uu____4696 =
                                                              let uu____4699
                                                                =
                                                                let uu____4702
                                                                  =
                                                                  let uu____4705
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4705
                                                                    (
                                                                    fun _4708
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4708)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4702
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4699
                                                               in
                                                            let uu____4709 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4696,
                                                              uu____4709))))
                                         | uu____4712 ->
                                             let uu____4713 =
                                               let uu____4719 =
                                                 let uu____4721 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4721
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4719)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4713 r
                                          in
                                       match uu____4591 with
                                       | (k,g_k) ->
                                           ((let uu____4738 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4738
                                             then
                                               let uu____4743 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4743
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4751 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4751
                                              then
                                                let uu____4756 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4756
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4769 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4769
                                                   in
                                                let repr_args t =
                                                  let uu____4790 =
                                                    let uu____4791 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4791.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4790 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4843 =
                                                        let uu____4844 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4844.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4843 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4853,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4863 ->
                                                           let uu____4864 =
                                                             let uu____4870 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4870)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4864 r)
                                                  | uu____4879 ->
                                                      let uu____4880 =
                                                        let uu____4886 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4886)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4880 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4896 =
                                                  let uu____4897 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4897.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4896 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4922 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4922 with
                                                     | (bs1,c1) ->
                                                         let uu____4929 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4929
                                                          with
                                                          | (us,a,is) ->
                                                              let ct =
                                                                {
                                                                  FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                  FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (
                                                                    ed.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                  FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                  FStar_Syntax_Syntax.flags
                                                                    = []
                                                                }  in
                                                              let uu____4940
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4940))
                                                | uu____4943 ->
                                                    let uu____4944 =
                                                      let uu____4950 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4950)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4944 r
                                                 in
                                              (let uu____4954 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4954
                                               then
                                                 let uu____4959 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4959
                                               else ());
                                              (let act2 =
                                                 let uu____4965 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4965 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___544_4979 =
                                                         act1  in
                                                       let uu____4980 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___544_4979.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___544_4979.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___544_4979.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4980
                                                       }
                                                     else
                                                       (let uu____4983 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4990
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4990
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4983
                                                        then
                                                          let uu___549_4995 =
                                                            act1  in
                                                          let uu____4996 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___549_4995.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___549_4995.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___549_4995.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___549_4995.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4996
                                                          }
                                                        else
                                                          (let uu____4999 =
                                                             let uu____5005 =
                                                               let uu____5007
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5009
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5007
                                                                 uu____5009
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5005)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4999 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5034 =
                      match uu____5034 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5079 =
                        let uu____5080 = tschemes_of repr  in
                        let uu____5085 = tschemes_of return_repr  in
                        let uu____5090 = tschemes_of bind_repr  in
                        let uu____5095 = tschemes_of stronger_repr  in
                        let uu____5100 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5080;
                          FStar_Syntax_Syntax.l_return = uu____5085;
                          FStar_Syntax_Syntax.l_bind = uu____5090;
                          FStar_Syntax_Syntax.l_subcomp = uu____5095;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5100
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5079  in
                    let uu___558_5105 = ed  in
                    let uu____5106 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___558_5105.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___558_5105.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___558_5105.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___558_5105.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5113 = signature  in
                         match uu____5113 with | (us,t,uu____5128) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5106;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___558_5105.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5166 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5166
         then
           let uu____5171 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5171
         else ());
        (let uu____5177 =
           let uu____5182 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5182 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5206 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5206  in
               let uu____5207 =
                 let uu____5214 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5214 bs  in
               (match uu____5207 with
                | (bs1,uu____5220,uu____5221) ->
                    let uu____5222 =
                      let tmp_t =
                        let uu____5232 =
                          let uu____5235 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5240  ->
                                 FStar_Pervasives_Native.Some _5240)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5235
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5232  in
                      let uu____5241 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5241 with
                      | (us,tmp_t1) ->
                          let uu____5258 =
                            let uu____5259 =
                              let uu____5260 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5260
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5259
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5258)
                       in
                    (match uu____5222 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5297 ->
                              let uu____5300 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5307 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5307 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5300
                              then (us, bs2)
                              else
                                (let uu____5318 =
                                   let uu____5324 =
                                     let uu____5326 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5328 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5326 uu____5328
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5324)
                                    in
                                 let uu____5332 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5318
                                   uu____5332))))
            in
         match uu____5177 with
         | (us,bs) ->
             let ed1 =
               let uu___592_5340 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___592_5340.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___592_5340.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___592_5340.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___592_5340.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___592_5340.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___592_5340.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5341 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5341 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5360 =
                    let uu____5365 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5365  in
                  (match uu____5360 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5386 =
                           match uu____5386 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5406 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5406 t  in
                               let uu____5415 =
                                 let uu____5416 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5416 t1  in
                               (us1, uu____5415)
                            in
                         let uu___606_5421 = ed1  in
                         let uu____5422 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5423 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5424 =
                           FStar_List.map
                             (fun a  ->
                                let uu___609_5432 = a  in
                                let uu____5433 =
                                  let uu____5434 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5434  in
                                let uu____5445 =
                                  let uu____5446 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5446  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___609_5432.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___609_5432.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___609_5432.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___609_5432.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5433;
                                  FStar_Syntax_Syntax.action_typ = uu____5445
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___606_5421.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___606_5421.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___606_5421.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___606_5421.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5422;
                           FStar_Syntax_Syntax.combinators = uu____5423;
                           FStar_Syntax_Syntax.actions = uu____5424;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___606_5421.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5458 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5458
                         then
                           let uu____5463 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5463
                         else ());
                        (let env =
                           let uu____5470 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5470
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5505 k =
                           match uu____5505 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5525 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5525 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5534 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5534 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5535 =
                                            let uu____5542 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5542 t1
                                             in
                                          (match uu____5535 with
                                           | (t2,uu____5544,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5547 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5547 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5563 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5565 =
                                                 let uu____5567 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5567
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5563 uu____5565
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5582 ->
                                               let uu____5583 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5590 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5590 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5583
                                               then (g_us, t3)
                                               else
                                                 (let uu____5601 =
                                                    let uu____5607 =
                                                      let uu____5609 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5611 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5609
                                                        uu____5611
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5607)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5601
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5619 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5619
                          then
                            let uu____5624 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5624
                          else ());
                         (let fresh_a_and_wp uu____5640 =
                            let fail1 t =
                              let uu____5653 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5653
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5669 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5669 with
                            | (uu____5680,signature1) ->
                                let uu____5682 =
                                  let uu____5683 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5683.FStar_Syntax_Syntax.n  in
                                (match uu____5682 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5693) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5722)::(wp,uu____5724)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5753 -> fail1 signature1)
                                 | uu____5754 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5768 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5768
                            then
                              let uu____5773 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5773
                            else ()  in
                          let ret_wp =
                            let uu____5779 = fresh_a_and_wp ()  in
                            match uu____5779 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5795 =
                                    let uu____5804 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5811 =
                                      let uu____5820 =
                                        let uu____5827 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5827
                                         in
                                      [uu____5820]  in
                                    uu____5804 :: uu____5811  in
                                  let uu____5846 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5795
                                    uu____5846
                                   in
                                let uu____5849 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5849
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5863 = fresh_a_and_wp ()  in
                             match uu____5863 with
                             | (a,wp_sort_a) ->
                                 let uu____5876 = fresh_a_and_wp ()  in
                                 (match uu____5876 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5892 =
                                          let uu____5901 =
                                            let uu____5908 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5908
                                             in
                                          [uu____5901]  in
                                        let uu____5921 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5892
                                          uu____5921
                                         in
                                      let k =
                                        let uu____5927 =
                                          let uu____5936 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5943 =
                                            let uu____5952 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5959 =
                                              let uu____5968 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5975 =
                                                let uu____5984 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5991 =
                                                  let uu____6000 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6000]  in
                                                uu____5984 :: uu____5991  in
                                              uu____5968 :: uu____5975  in
                                            uu____5952 :: uu____5959  in
                                          uu____5936 :: uu____5943  in
                                        let uu____6043 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5927
                                          uu____6043
                                         in
                                      let uu____6046 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6046
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6060 = fresh_a_and_wp ()  in
                              match uu____6060 with
                              | (a,wp_sort_a) ->
                                  let uu____6073 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6073 with
                                   | (t,uu____6079) ->
                                       let k =
                                         let uu____6083 =
                                           let uu____6092 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6099 =
                                             let uu____6108 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6115 =
                                               let uu____6124 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6124]  in
                                             uu____6108 :: uu____6115  in
                                           uu____6092 :: uu____6099  in
                                         let uu____6155 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6083
                                           uu____6155
                                          in
                                       let uu____6158 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6158
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6172 = fresh_a_and_wp ()  in
                               match uu____6172 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6186 =
                                       let uu____6189 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6189
                                        in
                                     let uu____6190 =
                                       let uu____6191 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6191
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6186
                                       uu____6190
                                      in
                                   let k =
                                     let uu____6203 =
                                       let uu____6212 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6219 =
                                         let uu____6228 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6235 =
                                           let uu____6244 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6251 =
                                             let uu____6260 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6260]  in
                                           uu____6244 :: uu____6251  in
                                         uu____6228 :: uu____6235  in
                                       uu____6212 :: uu____6219  in
                                     let uu____6297 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6203
                                       uu____6297
                                      in
                                   let uu____6300 =
                                     let uu____6305 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6305
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6300
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6337 = fresh_a_and_wp ()  in
                                match uu____6337 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6353 =
                                        let uu____6362 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6369 =
                                          let uu____6378 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6378]  in
                                        uu____6362 :: uu____6369  in
                                      let uu____6403 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6353
                                        uu____6403
                                       in
                                    let uu____6406 =
                                      let uu____6411 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6411
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6406
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6427 = fresh_a_and_wp ()  in
                                 match uu____6427 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6441 =
                                         let uu____6444 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6444
                                          in
                                       let uu____6445 =
                                         let uu____6446 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6446
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6441
                                         uu____6445
                                        in
                                     let wp_sort_b_a =
                                       let uu____6458 =
                                         let uu____6467 =
                                           let uu____6474 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6474
                                            in
                                         [uu____6467]  in
                                       let uu____6487 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6458
                                         uu____6487
                                        in
                                     let k =
                                       let uu____6493 =
                                         let uu____6502 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6509 =
                                           let uu____6518 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6525 =
                                             let uu____6534 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6534]  in
                                           uu____6518 :: uu____6525  in
                                         uu____6502 :: uu____6509  in
                                       let uu____6565 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6493
                                         uu____6565
                                        in
                                     let uu____6568 =
                                       let uu____6573 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6573
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6568
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6589 = fresh_a_and_wp ()  in
                                  match uu____6589 with
                                  | (a,wp_sort_a) ->
                                      let uu____6602 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6602 with
                                       | (t,uu____6608) ->
                                           let k =
                                             let uu____6612 =
                                               let uu____6621 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6628 =
                                                 let uu____6637 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6637]  in
                                               uu____6621 :: uu____6628  in
                                             let uu____6662 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6612 uu____6662
                                              in
                                           let trivial =
                                             let uu____6666 =
                                               let uu____6671 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6671 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6666
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6686 =
                                  let uu____6703 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6703 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6732 ->
                                      let repr =
                                        let uu____6736 = fresh_a_and_wp ()
                                           in
                                        match uu____6736 with
                                        | (a,wp_sort_a) ->
                                            let uu____6749 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6749 with
                                             | (t,uu____6755) ->
                                                 let k =
                                                   let uu____6759 =
                                                     let uu____6768 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6775 =
                                                       let uu____6784 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6784]  in
                                                     uu____6768 :: uu____6775
                                                      in
                                                   let uu____6809 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6759 uu____6809
                                                    in
                                                 let uu____6812 =
                                                   let uu____6817 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6817
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6812
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6861 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6861 with
                                          | (uu____6868,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6871 =
                                                let uu____6872 =
                                                  let uu____6889 =
                                                    let uu____6900 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____6917 =
                                                      let uu____6928 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____6928]  in
                                                    uu____6900 :: uu____6917
                                                     in
                                                  (repr2, uu____6889)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____6872
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6871
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____6994 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____6994 wp  in
                                        let destruct_repr t =
                                          let uu____7009 =
                                            let uu____7010 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7010.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7009 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7021,(t1,uu____7023)::
                                               (wp,uu____7025)::[])
                                              -> (t1, wp)
                                          | uu____7084 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7100 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7100
                                              FStar_Util.must
                                             in
                                          let uu____7127 = fresh_a_and_wp ()
                                             in
                                          match uu____7127 with
                                          | (a,uu____7135) ->
                                              let x_a =
                                                let uu____7141 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7141
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7147 =
                                                    let uu____7148 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7148
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____7157 =
                                                    let uu____7158 =
                                                      let uu____7167 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7167
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7176 =
                                                      let uu____7187 =
                                                        let uu____7196 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7196
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7187]  in
                                                    uu____7158 :: uu____7176
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7147 uu____7157
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7232 =
                                                  let uu____7241 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7248 =
                                                    let uu____7257 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7257]  in
                                                  uu____7241 :: uu____7248
                                                   in
                                                let uu____7282 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7232 uu____7282
                                                 in
                                              let uu____7285 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7285 with
                                               | (k1,uu____7293,uu____7294)
                                                   ->
                                                   let env1 =
                                                     let uu____7298 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7298
                                                      in
                                                   check_and_gen'
                                                     "return_repr"
                                                     Prims.int_one env1
                                                     return_repr_ts
                                                     (FStar_Pervasives_Native.Some
                                                        k1))
                                           in
                                        log_combinator "return_repr"
                                          return_repr;
                                        (let bind_repr =
                                           let bind_repr_ts =
                                             let uu____7311 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7311
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7349 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7349
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7350 = fresh_a_and_wp ()
                                              in
                                           match uu____7350 with
                                           | (a,wp_sort_a) ->
                                               let uu____7363 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7363 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7379 =
                                                        let uu____7388 =
                                                          let uu____7395 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7395
                                                           in
                                                        [uu____7388]  in
                                                      let uu____7408 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7379 uu____7408
                                                       in
                                                    let wp_f =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_f"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a
                                                       in
                                                    let wp_g =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_g"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a_b
                                                       in
                                                    let x_a =
                                                      let uu____7416 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7416
                                                       in
                                                    let wp_g_x =
                                                      let uu____7419 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g
                                                         in
                                                      let uu____7420 =
                                                        let uu____7421 =
                                                          let uu____7430 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7430
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7421]  in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7419 uu____7420
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7459 =
                                                          let uu____7460 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7460
                                                            FStar_Pervasives_Native.snd
                                                           in
                                                        let uu____7469 =
                                                          let uu____7470 =
                                                            let uu____7473 =
                                                              let uu____7476
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a
                                                                 in
                                                              let uu____7477
                                                                =
                                                                let uu____7480
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b
                                                                   in
                                                                let uu____7481
                                                                  =
                                                                  let uu____7484
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  let uu____7485
                                                                    =
                                                                    let uu____7488
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7488]
                                                                     in
                                                                  uu____7484
                                                                    ::
                                                                    uu____7485
                                                                   in
                                                                uu____7480 ::
                                                                  uu____7481
                                                                 in
                                                              uu____7476 ::
                                                                uu____7477
                                                               in
                                                            r :: uu____7473
                                                             in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7470
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7459
                                                          uu____7469
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7506 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7506
                                                      then
                                                        let uu____7517 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7524 =
                                                          let uu____7533 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7533]  in
                                                        uu____7517 ::
                                                          uu____7524
                                                      else []  in
                                                    let k =
                                                      let uu____7569 =
                                                        let uu____7578 =
                                                          let uu____7587 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7594 =
                                                            let uu____7603 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7603]  in
                                                          uu____7587 ::
                                                            uu____7594
                                                           in
                                                        let uu____7628 =
                                                          let uu____7637 =
                                                            let uu____7646 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7653 =
                                                              let uu____7662
                                                                =
                                                                let uu____7669
                                                                  =
                                                                  let uu____7670
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7670
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7669
                                                                 in
                                                              let uu____7671
                                                                =
                                                                let uu____7680
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7687
                                                                  =
                                                                  let uu____7696
                                                                    =
                                                                    let uu____7703
                                                                    =
                                                                    let uu____7704
                                                                    =
                                                                    let uu____7713
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7713]
                                                                     in
                                                                    let uu____7732
                                                                    =
                                                                    let uu____7735
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7735
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7704
                                                                    uu____7732
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7703
                                                                     in
                                                                  [uu____7696]
                                                                   in
                                                                uu____7680 ::
                                                                  uu____7687
                                                                 in
                                                              uu____7662 ::
                                                                uu____7671
                                                               in
                                                            uu____7646 ::
                                                              uu____7653
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7637
                                                           in
                                                        FStar_List.append
                                                          uu____7578
                                                          uu____7628
                                                         in
                                                      let uu____7780 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7569 uu____7780
                                                       in
                                                    let uu____7783 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7783 with
                                                     | (k1,uu____7791,uu____7792)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___804_7802
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___804_7802.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7804  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7804)
                                                            in
                                                         check_and_gen'
                                                           "bind_repr"
                                                           (Prims.of_int (2))
                                                           env2 bind_repr_ts
                                                           (FStar_Pervasives_Native.Some
                                                              k1)))
                                            in
                                         log_combinator "bind_repr" bind_repr;
                                         (let actions =
                                            let check_action act =
                                              if
                                                (FStar_List.length
                                                   act.FStar_Syntax_Syntax.action_params)
                                                  <> Prims.int_zero
                                              then
                                                failwith
                                                  "tc_eff_decl: expected action_params to be empty"
                                              else ();
                                              (let uu____7831 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7845 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7845 with
                                                    | (usubst,uvs) ->
                                                        let uu____7868 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7869 =
                                                          let uu___817_7870 =
                                                            act  in
                                                          let uu____7871 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7872 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___817_7870.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___817_7870.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___817_7870.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7871;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7872
                                                          }  in
                                                        (uu____7868,
                                                          uu____7869))
                                                  in
                                               match uu____7831 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7876 =
                                                       let uu____7877 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7877.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7876 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7903 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7903
                                                         then
                                                           let uu____7906 =
                                                             let uu____7909 =
                                                               let uu____7910
                                                                 =
                                                                 let uu____7911
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7911
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7910
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7909
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7906
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7934 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7935 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7935 with
                                                    | (act_typ1,uu____7943,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___834_7946 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___834_7946.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7949 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7949
                                                          then
                                                            let uu____7953 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7955 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7957 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7953
                                                              uu____7955
                                                              uu____7957
                                                          else ());
                                                         (let uu____7962 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7962
                                                          with
                                                          | (act_defn,uu____7970,g_a)
                                                              ->
                                                              let act_defn1 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                  env1
                                                                  act_defn
                                                                 in
                                                              let act_typ2 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                  FStar_TypeChecker_Env.Eager_unfolding;
                                                                  FStar_TypeChecker_Env.Beta]
                                                                  env1
                                                                  act_typ1
                                                                 in
                                                              let uu____7974
                                                                =
                                                                let act_typ3
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    act_typ2
                                                                   in
                                                                match 
                                                                  act_typ3.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8010
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8010
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8022)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8029
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8029
                                                                     in
                                                                    let uu____8032
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8032
                                                                    with
                                                                    | 
                                                                    (k1,uu____8046,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8050
                                                                    ->
                                                                    let uu____8051
                                                                    =
                                                                    let uu____8057
                                                                    =
                                                                    let uu____8059
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8061
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8059
                                                                    uu____8061
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8057)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8051
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____7974
                                                               with
                                                               | (expected_k,g_k)
                                                                   ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                   ((
                                                                    let uu____8079
                                                                    =
                                                                    let uu____8080
                                                                    =
                                                                    let uu____8081
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8081
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8080
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8079);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8083
                                                                    =
                                                                    let uu____8084
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8084.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8083
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8109
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8109
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8116
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8116
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8136
                                                                    =
                                                                    let uu____8137
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8137]
                                                                     in
                                                                    let uu____8138
                                                                    =
                                                                    let uu____8149
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8149]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8136;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8138;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8174
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8174))
                                                                    | 
                                                                    uu____8177
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8179
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8201
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8201))
                                                                     in
                                                                    match uu____8179
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___884_8220
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___884_8220.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___884_8220.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___884_8220.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))
                                               in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action)
                                             in
                                          ((FStar_Pervasives_Native.Some repr),
                                            (FStar_Pervasives_Native.Some
                                               return_repr),
                                            (FStar_Pervasives_Native.Some
                                               bind_repr), actions)))))
                                   in
                                match uu____6686 with
                                | (repr,return_repr,bind_repr,actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts
                                         in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs
                                         in
                                      let uu____8263 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8263 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else1;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp;
                                        FStar_Syntax_Syntax.trivial = trivial;
                                        FStar_Syntax_Syntax.repr = repr;
                                        FStar_Syntax_Syntax.return_repr =
                                          return_repr;
                                        FStar_Syntax_Syntax.bind_repr =
                                          bind_repr
                                      }  in
                                    let combinators1 =
                                      FStar_Syntax_Util.apply_wp_eff_combinators
                                        cl combinators
                                       in
                                    let combinators2 =
                                      match ed2.FStar_Syntax_Syntax.combinators
                                      with
                                      | FStar_Syntax_Syntax.Primitive_eff
                                          uu____8275 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8276 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8277 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___904_8280 = ed2  in
                                      let uu____8281 = cl signature  in
                                      let uu____8282 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___907_8290 = a  in
                                             let uu____8291 =
                                               let uu____8292 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8292
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8317 =
                                               let uu____8318 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8318
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___907_8290.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___907_8290.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___907_8290.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___907_8290.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8291;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8317
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___904_8280.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___904_8280.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___904_8280.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___904_8280.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8281;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8282;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___904_8280.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8344 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8344
                                      then
                                        let uu____8349 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8349
                                      else ());
                                     ed3)))))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      fun quals  ->
        let uu____8375 =
          let uu____8390 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8390 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8375 env ed quals
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____8440 =
          let uu____8441 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8447 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8441 uu____8447  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8491)::(wp,uu____8493)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8522 -> fail1 ())
        | uu____8523 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8536 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8536
       then
         let uu____8541 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8541
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8558 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8558.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8570 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8574 =
                let uu____8575 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8575 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8574
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8584 =
                   let uu____8585 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8585 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8584
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8593 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8593))
           in
        if uu____8570
        then
          let uu____8596 =
            let uu____8602 =
              let uu____8604 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8607 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8604 uu____8607
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8602)  in
          FStar_Errors.raise_error uu____8596 r
        else ());
       (let uu____8614 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8614 with
        | (us,lift,lift_ty) ->
            ((let uu____8628 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8628
              then
                let uu____8633 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8639 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8633 uu____8639
              else ());
             (let uu____8648 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8648 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8666 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.source
                         in
                      let uu____8668 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.target
                         in
                      let uu____8670 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8666 uu____8668 s uu____8670
                       in
                    let uu____8673 =
                      let uu____8680 =
                        let uu____8685 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8685
                          (fun uu____8702  ->
                             match uu____8702 with
                             | (t,u) ->
                                 let uu____8713 =
                                   let uu____8714 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8714
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8713, u))
                         in
                      match uu____8680 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____8733 =
                              let uu____8734 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____8734.FStar_Syntax_Syntax.n  in
                            match uu____8733 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8746)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____8774 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____8774 with
                                 | (a',uu____8784)::bs1 ->
                                     let uu____8804 =
                                       let uu____8805 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____8805
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____8871 =
                                       let uu____8884 =
                                         let uu____8887 =
                                           let uu____8888 =
                                             let uu____8895 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____8895)  in
                                           FStar_Syntax_Syntax.NT uu____8888
                                            in
                                         [uu____8887]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____8884
                                        in
                                     FStar_All.pipe_right uu____8804
                                       uu____8871)
                            | uu____8910 ->
                                let uu____8911 =
                                  let uu____8917 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____8917)
                                   in
                                FStar_Errors.raise_error uu____8911 r
                             in
                          let uu____8929 =
                            let uu____8940 =
                              let uu____8945 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____8952 =
                                let uu____8953 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____8953
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____8945 r sub1.FStar_Syntax_Syntax.source
                                u_a uu____8952
                               in
                            match uu____8940 with
                            | (f_sort,g) ->
                                let uu____8974 =
                                  let uu____8981 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____8981
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____8974, g)
                             in
                          (match uu____8929 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9048 =
                                 let uu____9053 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9054 =
                                   let uu____9055 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9055
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9053 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____9054
                                  in
                               (match uu____9048 with
                                | (repr,g_repr) ->
                                    let uu____9072 =
                                      let uu____9077 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9078 =
                                        let uu____9080 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9082 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9080 uu____9082
                                         in
                                      pure_wp_uvar uu____9077 repr uu____9078
                                        r
                                       in
                                    (match uu____9072 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9094 =
                                             let uu____9095 =
                                               let uu____9096 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9096]  in
                                             let uu____9097 =
                                               let uu____9108 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9108]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9095;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9097;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9094
                                            in
                                         let uu____9141 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9144 =
                                           let uu____9145 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9145 guard_wp
                                            in
                                         (uu____9141, uu____9144))))
                       in
                    match uu____8673 with
                    | (k,g_k) ->
                        ((let uu____9155 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9155
                          then
                            let uu____9160 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9160
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9169 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9169
                           then
                             let uu____9174 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9174
                           else ());
                          (let sub2 =
                             let uu___1000_9180 = sub1  in
                             let uu____9181 =
                               let uu____9184 =
                                 let uu____9185 =
                                   let uu____9188 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9188
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9185)  in
                               FStar_Pervasives_Native.Some uu____9184  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1000_9180.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1000_9180.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9181;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9200 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9200
                            then
                              let uu____9205 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9205
                            else ());
                           sub2)))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9242 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9242  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9245 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9245
        then tc_layered_lift env sub1
        else
          (let uu____9252 =
             let uu____9259 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9259
              in
           match uu____9252 with
           | (a,wp_a_src) ->
               let uu____9266 =
                 let uu____9273 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9273
                  in
               (match uu____9266 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9281 =
                        let uu____9284 =
                          let uu____9285 =
                            let uu____9292 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9292)  in
                          FStar_Syntax_Syntax.NT uu____9285  in
                        [uu____9284]  in
                      FStar_Syntax_Subst.subst uu____9281 wp_b_tgt  in
                    let expected_k =
                      let uu____9300 =
                        let uu____9309 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9316 =
                          let uu____9325 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9325]  in
                        uu____9309 :: uu____9316  in
                      let uu____9350 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9300 uu____9350  in
                    let repr_type eff_name a1 wp =
                      (let uu____9372 =
                         let uu____9374 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9374  in
                       if uu____9372
                       then
                         let uu____9377 =
                           let uu____9383 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9383)
                            in
                         let uu____9387 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9377 uu____9387
                       else ());
                      (let uu____9390 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9390 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9423 =
                               let uu____9424 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9424
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9423
                              in
                           let uu____9431 =
                             let uu____9432 =
                               let uu____9449 =
                                 let uu____9460 =
                                   FStar_Syntax_Syntax.as_arg a1  in
                                 let uu____9469 =
                                   let uu____9480 =
                                     FStar_Syntax_Syntax.as_arg wp  in
                                   [uu____9480]  in
                                 uu____9460 :: uu____9469  in
                               (repr, uu____9449)  in
                             FStar_Syntax_Syntax.Tm_app uu____9432  in
                           let uu____9525 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Syntax_Syntax.mk uu____9431 uu____9525)
                       in
                    let uu____9526 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9699 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9710 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9710 with
                              | (usubst,uvs1) ->
                                  let uu____9733 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9734 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9733, uu____9734)
                            else (env, lift_wp)  in
                          (match uu____9699 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9784 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9784))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9855 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9870 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9870 with
                              | (usubst,uvs) ->
                                  let uu____9895 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9895)
                            else ([], lift)  in
                          (match uu____9855 with
                           | (uvs,lift1) ->
                               ((let uu____9931 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9931
                                 then
                                   let uu____9935 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9935
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9941 =
                                   let uu____9948 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9948 lift1
                                    in
                                 match uu____9941 with
                                 | (lift2,comp,uu____9973) ->
                                     let uu____9974 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____9974 with
                                      | (uu____10003,lift_wp,lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp
                                             in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab
                                             in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____10035 =
                                              let uu____10046 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10046
                                               in
                                            let uu____10063 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10035, uu____10063)
                                          else
                                            (let uu____10092 =
                                               let uu____10103 =
                                                 let uu____10112 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10112)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10103
                                                in
                                             let uu____10127 =
                                               let uu____10136 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10136)  in
                                             (uu____10092, uu____10127))))))
                       in
                    (match uu____9526 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1084_10200 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1084_10200.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1084_10200.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1084_10200.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1084_10200.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1084_10200.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1084_10200.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1084_10200.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1084_10200.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1084_10200.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1084_10200.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1084_10200.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1084_10200.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1084_10200.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1084_10200.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1084_10200.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1084_10200.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1084_10200.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1084_10200.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1084_10200.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1084_10200.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1084_10200.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1084_10200.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1084_10200.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1084_10200.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1084_10200.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1084_10200.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1084_10200.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1084_10200.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1084_10200.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1084_10200.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1084_10200.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1084_10200.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1084_10200.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1084_10200.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1084_10200.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1084_10200.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1084_10200.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1084_10200.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1084_10200.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1084_10200.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1084_10200.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1084_10200.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1084_10200.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1084_10200.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1084_10200.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1084_10200.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10233 =
                                 let uu____10238 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10238 with
                                 | (usubst,uvs1) ->
                                     let uu____10261 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10262 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10261, uu____10262)
                                  in
                               (match uu____10233 with
                                | (env2,lift2) ->
                                    let uu____10267 =
                                      let uu____10274 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10274
                                       in
                                    (match uu____10267 with
                                     | (a1,wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1
                                            in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1
                                            in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a
                                            in
                                         let repr_f =
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ
                                            in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp)
                                              in
                                           let lift_wp_a =
                                             let uu____10300 =
                                               let uu____10301 =
                                                 let uu____10318 =
                                                   let uu____10329 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ
                                                      in
                                                   let uu____10338 =
                                                     let uu____10349 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ
                                                        in
                                                     [uu____10349]  in
                                                   uu____10329 :: uu____10338
                                                    in
                                                 (lift_wp1, uu____10318)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10301
                                                in
                                             let uu____10394 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10300 uu____10394
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10398 =
                                             let uu____10407 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10414 =
                                               let uu____10423 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10430 =
                                                 let uu____10439 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10439]  in
                                               uu____10423 :: uu____10430  in
                                             uu____10407 :: uu____10414  in
                                           let uu____10470 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10398 uu____10470
                                            in
                                         let uu____10473 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10473 with
                                          | (expected_k2,uu____10483,uu____10484)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10492 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10492))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10500 =
                             let uu____10502 =
                               let uu____10504 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10504
                                 FStar_List.length
                                in
                             uu____10502 <> Prims.int_one  in
                           if uu____10500
                           then
                             let uu____10527 =
                               let uu____10533 =
                                 let uu____10535 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10537 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10539 =
                                   let uu____10541 =
                                     let uu____10543 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10543
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10541
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10535 uu____10537 uu____10539
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10533)
                                in
                             FStar_Errors.raise_error uu____10527 r
                           else ());
                          (let uu____10570 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10573 =
                                  let uu____10575 =
                                    let uu____10578 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10578
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10575
                                    FStar_List.length
                                   in
                                uu____10573 <> Prims.int_one)
                              in
                           if uu____10570
                           then
                             let uu____10617 =
                               let uu____10623 =
                                 let uu____10625 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10627 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10629 =
                                   let uu____10631 =
                                     let uu____10633 =
                                       let uu____10636 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10636
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10633
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10631
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10625 uu____10627 uu____10629
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10623)
                                in
                             FStar_Errors.raise_error uu____10617 r
                           else ());
                          (let uu___1121_10678 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1121_10678.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1121_10678.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           })))))
  
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun uu____10709  ->
      fun r  ->
        match uu____10709 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10732 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10760 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10760 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10791 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10791 c  in
                     let uu____10800 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10800, uvs1, tps1, c1))
               in
            (match uu____10732 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10820 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10820 with
                  | (tps2,c2) ->
                      let uu____10835 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10835 with
                       | (tps3,env3,us) ->
                           let uu____10853 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10853 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10879)::uu____10880 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10899 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10907 =
                                    let uu____10909 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10909  in
                                  if uu____10907
                                  then
                                    let uu____10912 =
                                      let uu____10918 =
                                        let uu____10920 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10922 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10920 uu____10922
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10918)
                                       in
                                    FStar_Errors.raise_error uu____10912 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10930 =
                                    let uu____10931 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10931
                                     in
                                  match uu____10930 with
                                  | (uvs2,t) ->
                                      let uu____10960 =
                                        let uu____10965 =
                                          let uu____10978 =
                                            let uu____10979 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____10979.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____10978)  in
                                        match uu____10965 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____10994,c5)) -> ([], c5)
                                        | (uu____11036,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11075 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____10960 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11107 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11107 with
                                               | (uu____11112,t1) ->
                                                   let uu____11114 =
                                                     let uu____11120 =
                                                       let uu____11122 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11124 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11128 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11122
                                                         uu____11124
                                                         uu____11128
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11120)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11114 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11170 = FStar_Ident.string_of_lid m  in
              let uu____11172 = FStar_Ident.string_of_lid n1  in
              let uu____11174 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11170 uu____11172
                uu____11174
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11182 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11182 with
            | (us,t,ty) ->
                let uu____11198 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11198 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11211 =
                         let uu____11216 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11216
                           (fun uu____11233  ->
                              match uu____11233 with
                              | (t1,u) ->
                                  let uu____11244 =
                                    let uu____11245 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11245
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11244, u))
                          in
                       match uu____11211 with
                       | (a,u_a) ->
                           let uu____11253 =
                             let uu____11258 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11258
                               (fun uu____11275  ->
                                  match uu____11275 with
                                  | (t1,u) ->
                                      let uu____11286 =
                                        let uu____11287 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11287
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11286, u))
                              in
                           (match uu____11253 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11304 =
                                    let uu____11305 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11305.FStar_Syntax_Syntax.n  in
                                  match uu____11304 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11317) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11345 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11345 with
                                       | (a',uu____11355)::(b',uu____11357)::bs1
                                           ->
                                           let uu____11387 =
                                             let uu____11388 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11388
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11454 =
                                             let uu____11467 =
                                               let uu____11470 =
                                                 let uu____11471 =
                                                   let uu____11478 =
                                                     let uu____11481 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11481
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11478)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11471
                                                  in
                                               let uu____11494 =
                                                 let uu____11497 =
                                                   let uu____11498 =
                                                     let uu____11505 =
                                                       let uu____11508 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11508
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11505)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11498
                                                    in
                                                 [uu____11497]  in
                                               uu____11470 :: uu____11494  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11467
                                              in
                                           FStar_All.pipe_right uu____11387
                                             uu____11454)
                                  | uu____11529 ->
                                      let uu____11530 =
                                        let uu____11536 =
                                          let uu____11538 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11540 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11538 uu____11540
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11536)
                                         in
                                      FStar_Errors.raise_error uu____11530 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11573 =
                                  let uu____11584 =
                                    let uu____11589 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11590 =
                                      let uu____11591 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11591
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11589 r m u_a uu____11590
                                     in
                                  match uu____11584 with
                                  | (repr,g) ->
                                      let uu____11612 =
                                        let uu____11619 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11619
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11612, g)
                                   in
                                (match uu____11573 with
                                 | (f,guard_f) ->
                                     let uu____11651 =
                                       let x_a =
                                         let uu____11669 =
                                           let uu____11670 =
                                             let uu____11671 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11671
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11670
                                            in
                                         FStar_All.pipe_right uu____11669
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11687 =
                                         let uu____11692 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11711 =
                                           let uu____11712 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11712
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11692 r n1 u_b uu____11711
                                          in
                                       match uu____11687 with
                                       | (repr,g) ->
                                           let uu____11733 =
                                             let uu____11740 =
                                               let uu____11741 =
                                                 let uu____11742 =
                                                   let uu____11745 =
                                                     let uu____11748 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11748
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11745
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11742
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11741
                                                in
                                             FStar_All.pipe_right uu____11740
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____11733, g)
                                        in
                                     (match uu____11651 with
                                      | (g,guard_g) ->
                                          let uu____11792 =
                                            let uu____11797 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____11798 =
                                              let uu____11799 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11799
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11797 r p u_b uu____11798
                                             in
                                          (match uu____11792 with
                                           | (repr,guard_repr) ->
                                               let uu____11814 =
                                                 let uu____11819 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____11820 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____11819
                                                   repr uu____11820 r
                                                  in
                                               (match uu____11814 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____11832 =
                                                        let uu____11835 =
                                                          let uu____11836 =
                                                            let uu____11837 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____11837]  in
                                                          let uu____11838 =
                                                            let uu____11849 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____11849]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____11836;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____11838;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____11835
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____11832
                                                       in
                                                    let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 ty1 k
                                                       in
                                                    (FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1)
                                                       [guard_f;
                                                       guard_g;
                                                       guard_repr;
                                                       g_pure_wp_uvar;
                                                       guard_eq];
                                                     (let uu____11909 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____11909
                                                      then
                                                        let uu____11913 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____11919 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____11913
                                                          uu____11919
                                                      else ());
                                                     (let uu____11929 =
                                                        let uu____11935 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____11935)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____11929);
                                                     (let uu____11939 =
                                                        let uu____11940 =
                                                          let uu____11943 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____11943
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____11940)
                                                         in
                                                      ((us1, t), uu____11939)))))))))))
  