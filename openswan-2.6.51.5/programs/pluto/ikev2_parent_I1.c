/*
 * IKEv2 parent SA creation routines --- outI1 routines
 * Copyright (C) 2007-2017 Michael Richardson <mcr@xelerance.com>
 * Copyright (C) 2008-2011 Paul Wouters <paul@xelerance.com>
 * Copyright (C) 2008 Antony Antony <antony@xelerance.com>
 * Copyright (C) 2008-2009 David McCullough <david_mccullough@securecomputing.com>
 * Copyright (C) 2010,2012 Avesh Agarwal <avagarwa@redhat.com>
 * Copyright (C) 2010 Tuomo Soini <tis@foobar.fi
 * Copyright (C) 2012 Paul Wouters <pwouters@redhat.com>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2 of the License, or (at your
 * option) any later version.  See <http://www.fsf.org/copyleft/gpl.txt>.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * for more details.
 *
 */


/* This file is #include'ed into ikev2_parent.c */

static void ikev2_parent_outI1_continue(struct pluto_crypto_req_cont *pcrc
                                        , struct pluto_crypto_req *r
                                        , err_t ugh);

static stf_status ikev2_parent_outI1_tail(struct pluto_crypto_req_cont *pcrc
                                          , struct pluto_crypto_req *r);

static stf_status ikev2_parent_outI1_common(struct msg_digest *md
                                            , struct state *st);

/*
 *
 ***************************************************************
 *****                   PARENT_OUTI1                      *****
 ***************************************************************
 *
 *
 * Initiate an Oakley Main Mode exchange.
 *       HDR, SAi1, KEi, Ni   -->
 *
 * Note: this is not called from demux.c, but from ipsecdoi_initiate().
 *
 */
stf_status
ikev2parent_outI1(int whack_sock
                  , struct connection *c
                  , struct state *predecessor
                  , so_serial_t  *newstateno
                  , lset_t policy
                  , unsigned long try
                  , enum crypto_importance importance
                  , struct xfrm_user_sec_ctx_ike * uctx UNUSED
                  )
{
    struct state *st = new_state();
    /*发起端随机生成cookie值*/
    get_cookie(TRUE, st->st_icookie, COOKIE_SIZE, &c->spd.that.host_addr);

	/*将连接上的信息初始化到状态上*/
    initialize_new_state(st, c, policy, try, whack_sock, importance);

    if(newstateno) *newstateno = st->st_serialno;

   /*
 * initialize the local end point address, so that NAT calculation will
 * have something to work with.
 *
 *在set_state_ike_endpoints中将隧道两端的地址更新到了st_localaddr，st_port上
 *这里再次修改为出接口的地址和端口，暂不清楚用意
 */
    st->st_localaddr = st->st_interface->ip_addr;
    st->st_localport = st->st_interface->port;

    return
        ikev2parent_outI1_withstate(st, whack_sock, c
                                    , predecessor, policy
                                    , try, importance
                                    , uctx);
}

stf_status
ikev2parent_outI1_withstate(struct state *st
                            , int whack_sock
                            , struct connection *c
                            , struct state *predecessor
                            , lset_t policy
                            , unsigned long try /* how many attempts so far */
                            , enum crypto_importance importance
                            , struct xfrm_user_sec_ctx_ike * uctx UNUSED
                            )
{
    struct db_sa *sadb;
    int    groupnum;
    int    need_to_add_pending = 0;
	/*根据配置的策略索引找到对应的SADB模板*/
    int    policy_index = POLICY_ISAKMP(policy
                                        , c->spd.this.xauth_server
                                        , c->spd.this.xauth_client);

    /* set up new state */
    st->st_ikev2 = TRUE;/*用来标记是否为IKEv2*/
    change_state(st, STATE_PARENT_I1);/*当前状态为STATE_PARENT_I1*/
    st->st_try   = try;

    /* IKE version numbers -- used mostly in logging */
    st->st_ike_maj        = IKEv2_MAJOR_VERSION;
    st->st_ike_min        = IKEv2_MINOR_VERSION;
    st->st_policy         = policy & ~POLICY_IPSEC_MASK;
    st->st_ikev2_orig_initiator = TRUE;

    if (HAS_IPSEC_POLICY(policy))
        need_to_add_pending = 1;

    if (predecessor == NULL)
        openswan_log("initiating v2 parent SA");
    else
        openswan_log("initiating v2 parent SA to replace #%lu", predecessor->st_serialno);

    if (predecessor != NULL) {
        /* replace the existing pending SA */
        int rc = update_pending(predecessor, st);
        loglog(RC_NEW_STATE + STATE_PARENT_I1
               , "%s: initiate, replacing #%lu %s"
               , enum_name(&state_names, st->st_state)
               , predecessor->st_serialno
               , rc ? "-- marked as pending up" : "-- in progress");
        /* should the update fail, flag that an add is needed */
        if (rc) {
            if (!HAS_IPSEC_POLICY(policy)) {
                if (HAS_IPSEC_POLICY(c->policy)) {
                    /* this is a parent SA being rekeyd; we don't have a
                     * pending entry to update; which means the other side
                     * was the original initiator; we need to create a new
                     * pending entry with ipsec policy, which we can get
                     * from the existing connection */
                    policy |= c->policy & POLICY_IPSEC_MASK;
                }
            }

            need_to_add_pending = 1;
        }

    } else {
            loglog(RC_NEW_STATE + STATE_PARENT_I1
                      , "%s: initiate", enum_name(&state_names, st->st_state));
    }

    if (need_to_add_pending) {
#ifdef HAVE_LABELED_IPSEC
        st->sec_ctx = NULL;
        if( uctx != NULL) {
            openswan_log("Labeled ipsec is not supported with ikev2 yet");
        }
#endif

        add_pending(dup_any(whack_sock), st, c, policy, 1
                    , predecessor == NULL? SOS_NOBODY : predecessor->st_serialno
                    , st->sec_ctx
                    );
    }

    /*
     * now, we need to initialize st->st_oakley, specifically, the group
     * number needs to be initialized.
     */
    groupnum = 0;

    st->st_sadb = &oakley_sadb[policy_index];
	/*根据配置信息alg_info_ike生成相应的sadb*/
    sadb = oakley_alg_makedb(st->st_connection->alg_info_ike
                             , st->st_sadb, 0);
    if(sadb != NULL) {
        st->st_sadb = sadb;
    }
	/*由于ikev1和ikev2的SA载荷的结构不一致，因此需要做一个转换*/
    sadb = st->st_sadb = sa_v2_convert(st->st_sadb);
	
    {
        unsigned int  pc_cnt;

        /* look at all the proposals */
        if(st->st_sadb->prop_disj!=NULL) {/*获取SA载荷中采用的DH组，只获取第一个DH即可*/
            for(pc_cnt=0; pc_cnt < st->st_sadb->prop_disj_cnt && groupnum==0;
                pc_cnt++)
                {
                    struct db_v2_prop *vp = &st->st_sadb->prop_disj[pc_cnt];
                    unsigned int pr_cnt;

                    /* look at all the proposals */
                    if(vp->props!=NULL) {
                        for(pr_cnt=0; pr_cnt < vp->prop_cnt && groupnum==0; pr_cnt++)
                            {
                                unsigned int ts_cnt;
                                struct db_v2_prop_conj *vpc = &vp->props[pr_cnt];

                                for(ts_cnt=0; ts_cnt < vpc->trans_cnt && groupnum==0; ts_cnt++) {
                                    struct db_v2_trans *tr = &vpc->trans[ts_cnt];
                                    if(tr!=NULL&& tr->transform_type == IKEv2_TRANS_TYPE_DH) {
                                        groupnum = tr->transid;
                                    }
                                }
                            }
                    }
                }
        }
    }
    if(groupnum == 0) {
        groupnum = OAKLEY_GROUP_MODP2048;/*如果未设置DH组，则默认使用MODP2048,这里是猜想!!!*/
    }
    st->st_oakley.group=lookup_group(groupnum);
    st->st_oakley.groupnum=groupnum;

    /* now. we need to go calculate the nonce, and the KE */
    {
        struct ke_continuation *ke = alloc_thing(struct ke_continuation
                                                 , "ikev2_outI1 KE");
        stf_status e;

        ke->md = alloc_md();
        ke->md->from_state = STATE_IKEv2_BASE;
        ke->md->svm = &ikev2_parent_firststate_microcode;
        ke->md->st = st;
        set_suspended(st, ke->md);

        if (!st->st_sec_in_use) {/* st_sec_in_use ???*/
            pcrc_init(&ke->ke_pcrc);
            ke->ke_pcrc.pcrc_func = ikev2_parent_outI1_continue;
			/*计算KE需要确定使用的DH组,因此使用了st->st_oakley.group*/
            e = build_ke(&ke->ke_pcrc, st, st->st_oakley.group, importance);
            if( (e != STF_SUSPEND && e != STF_INLINE) || (e == STF_TOOMUCHCRYPTO)) {
                loglog(RC_CRYPTOFAILED, "system too busy - Enabling dcookies [TODO]");
                delete_state(st);
            }
        } else {
            /* this case is that st_sec already is initialized */
            e = ikev2_parent_outI1_tail((struct pluto_crypto_req_cont *)ke
                                        , NULL);
        }

        reset_globals();

        return e;
    }
}

static void
ikev2_parent_outI1_continue(struct pluto_crypto_req_cont *pcrc
                            , struct pluto_crypto_req *r
                            , err_t ugh)
{
    struct ke_continuation *ke = (struct ke_continuation *)pcrc;
    struct msg_digest *md = ke->md;
    struct state *const st = md->st;
    stf_status e;

    DBG(DBG_CONTROLMORE
        , DBG_log("ikev2 parent outI1: calculated ke+nonce, sending I1"));

    if (st == NULL) {
        loglog(RC_LOG_SERIOUS, "%s: Request was disconnected from state",
               __FUNCTION__);
        if (ke->md)
            release_md(ke->md);
        return;
    }

    /* XXX should check out ugh */
    passert(ugh == NULL);
    passert(cur_state == NULL);
    passert(st != NULL);

    passert(st->st_suspended_md == ke->md);
    set_suspended(st,NULL);	/* no longer connected or suspended */

    set_cur_state(st);

    st->st_calculating = FALSE;

    e = ikev2_parent_outI1_tail(pcrc, r);

    if(ke->md != NULL) {
        complete_v2_state_transition(&ke->md, e);
        if(ke->md) release_md(ke->md);
    }
    reset_cur_state();
    reset_globals();

    passert(GLOBALS_ARE_RESET());
}


static stf_status
ikev2_parent_outI1_tail(struct pluto_crypto_req_cont *pcrc
                        , struct pluto_crypto_req *r)
{
    struct ke_continuation *ke = (struct ke_continuation *)pcrc;
    struct msg_digest *md = ke->md;
    struct state *const st = md->st;

    unpack_v2KE(st, r, &st->st_gi);/*获取发起端DH算法的公共值：gi*/
    unpack_nonce(&st->st_ni, r);/*获取发起端Nonce值：ni*/
    return ikev2_parent_outI1_common(md, st);
}


static stf_status
ikev2_parent_outI1_common(struct msg_digest *md
                          , struct state *st)
{
    /* struct connection *c = st->st_connection; */
    int numvidtosend = 0;
#ifdef PLUTO_SENDS_VENDORID
    numvidtosend++;  /* if we need to send Openswan VID */
#endif

    /* set up reply */
/*
*	reply_buffer：真正开辟的内存空间，用来存储报文
*	reply_stream：可以简单的认为是个指针，记录已经使用的位置
*
**/
    init_pbs(&reply_stream, reply_buffer, sizeof(reply_buffer), "reply packet");

/*1. 构造HDR头部*/
    {
        struct isakmp_hdr hdr;

        zero(&hdr);        /* default to 0 */
        /* testing fake major new IKE version, should fail */

        if(DBGP(IMPAIR_MAJOR_VERSION_BUMP))
            hdr.isa_version = IKEv2_MAJOR_BUMP << ISA_MAJ_SHIFT | IKEv2_MINOR_VERSION;

        /* testing fake minor new IKE version, should success */
        else if(DBGP(IMPAIR_MINOR_VERSION_BUMP))
            hdr.isa_version = IKEv2_MAJOR_VERSION << ISA_MAJ_SHIFT | IKEv2_MINOR_BUMP;
        else {

            /* normal production case with real version */
            hdr.isa_version = IKEv2_MAJOR_VERSION << ISA_MAJ_SHIFT | IKEv2_MINOR_VERSION;
        }

        hdr.isa_xchg = ISAKMP_v2_SA_INIT;
        hdr.isa_flags = IKEv2_ORIG_INITIATOR_FLAG(st);
        memcpy(hdr.isa_icookie, st->st_icookie, COOKIE_SIZE);
        /* R-cookie, msgid are left zero */

        if (!out_struct(&hdr, &isakmp_hdr_desc, &reply_stream, &md->rbody))
            {
                reset_cur_state();
                return STF_INTERNAL_ERROR;
            }
    }



    /* send an anti DOS cookie, 4306 2.6, if we have received one from the
     * responder
     */

    if(st->st_dcookie.ptr) {
        chunk_t child_spi;
        memset(&child_spi, 0, sizeof(child_spi));
	/*
	*anti Dos时通过在报文中添加一个通知载荷，里面包含对端的cookie信息(st->st_dcookie)
	*
	* HDR头部中的np字段填充的是设么????? --->ship_v2N -->pbs_set_np -->out_struct
	*/
        ship_v2N(ISAKMP_NEXT_NONE, ISAKMP_PAYLOAD_NONCRITICAL, PROTO_ISAKMP,
                 &child_spi, v2N_COOKIE, &st->st_dcookie, &md->rbody);
    }

    /* SA out */
    {
        u_char *sa_start = md->rbody.cur;

        /* if we  have an OpenPGP certificate we assume an
         * OpenPGP peer and have to send the Vendor ID
         */
         /*
		*
		*	如何判断一个SA是ikev1 or ikev2的结构???
		*/
        if(st->st_sadb->prop_disj_cnt == 0 || st->st_sadb->prop_disj) {/*SA结构未转换???*/
            st->st_sadb = sa_v2_convert(st->st_sadb);
        }

        if (!ikev2_out_sa(&md->rbody
                          , PROTO_ISAKMP
                          , st->st_sadb
                          , st, TRUE /* parentSA */
                          , ISAKMP_NEXT_v2KE))
            {
                openswan_log("outsa fail");
                reset_cur_state();
                return STF_INTERNAL_ERROR;
            }
        /* save initiator SA for later HASH */
        if(st->st_p1isa.ptr == NULL)        /* no leak!  (MUST be first time) */
            {
                clonetochunk(st->st_p1isa, sa_start, md->rbody.cur - sa_start
                             , "sa in main_outI1");
            }
    }

    /* send KE */
    if(!justship_v2KE(st, &st->st_gi, st->st_oakley.groupnum,  &md->rbody, 0))
        return STF_INTERNAL_ERROR;


    /* send NONCE */
    if(!justship_v2Nonce(st, &md->rbody, &st->st_ni, 0)) {
        return STF_INTERNAL_ERROR;
    }

    if(!justship_v2nat(st, &md->rbody)) {/*填充NAT-D载荷*/
        return STF_INTERNAL_ERROR;
    }

    /* Send Vendor VID if needed */
    {/*省略了NAT-T的VID???*/
    /*pluto_vendorid在init_pluto_vendorid()完成了初始化*/
        pbs_set_np(&md->rbody,  ISAKMP_NEXT_v2V);
        if (!out_generic_raw(0, &isakmp_vendor_id_desc, &md->rbody
                             , pluto_vendorid, strlen(pluto_vendorid), "Vendor ID"))/*pluto_vendorid内容并不是真正的VID*/
            return STF_INTERNAL_ERROR;
    }

    close_message(&md->rbody);
    close_output_pbs(&reply_stream);

    /* let TCL hack it before we mark the length and copy it */
    TCLCALLOUT("v2_avoidEmitting", st, st->st_connection, md);

    freeanychunk(st->st_tpacket);
    clonetochunk(st->st_tpacket, reply_stream.start, pbs_offset(&reply_stream)
                 , "reply packet for ikev2_parent_outI1_tail");

    /* save packet for later signing *//*将第一个报文保存起来*/
    freeanychunk(st->st_firstpacket_me);
    clonetochunk(st->st_firstpacket_me, reply_stream.start
                 , pbs_offset(&reply_stream), "saved first packet");

    /* Transmit */
    send_packet(st, __FUNCTION__, TRUE);

    /* Set up a retransmission event, half a minute henceforth */
    TCLCALLOUT("v2_adjustTimers", st, st->st_connection, md);

#ifdef TPM
 tpm_stolen:
 tpm_ignore:
#endif
    delete_event(st);
    event_schedule(EVENT_v2_RETRANSMIT, EVENT_RETRANSMIT_DELAY_0, st);

    reset_cur_state();
    return STF_OK;
}

/*
 * Local Variables:
 * c-basic-offset:4
 * c-style: pluto
 * End:
 */
