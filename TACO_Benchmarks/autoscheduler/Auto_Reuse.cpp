  #include <iostream>
  #include <vector>
  //#include <algorithm>
  #include "limits.h"
  #include "float.h"
  #include <map>
  #include "clock.h"
  //#define vdsr
  //#define debug





  #include <algorithm>
  #include <regex>

  #include "AutoSchedule.h"
  #include "AutoScheduleUtils.h"
  #include "ExprUsesVar.h"
  #include "FindCalls.h"
  #include "Func.h"
  #include "IREquality.h"
  #include "Inline.h"
  #include "ParallelRVar.h"
  #include "RealizationOrder.h"
  #include "RegionCosts.h"
  #include "Scope.h"
  #include "Simplify.h"
  #include "Util.h"
  #define tile 8
  using namespace std;
  namespace Halide {
    namespace Internal {

      using std::deque;
      using std::make_pair;
      using std::map;
      using std::pair;
      using std::set;
      using std::string;
      using std::vector;

      namespace {

  // Substitute parameter estimates into the exprs describing the box bounds.
        void substitute_estimates_box(Box &box) {
          box.used = subsitute_var_estimates(box.used);
          for (auto &b : box.bounds) {
            b.min = subsitute_var_estimates(b.min);
            b.max = subsitute_var_estimates(b.max);
          }
        }

  // Substitute parameter estimates into the boxes in 'region'.
        void substitute_estimates_region(map<string, Box> &region) {
          for (auto &iter : region) {
            substitute_estimates_box(iter.second);
          }
        }

  // Return true if any of the box dimension is unbounded.
        bool is_box_unbounded(const Box &b) {
          for (size_t i = 0; i < b.size(); i++) {
            if (!b[i].is_bounded()) {
              return true;
            }
          }
          return false;
        }

  // Helper function to simplify the upper and lower bounds of each dimension of a box.
        void simplify_box(Box &b) {
          for (size_t i = 0; i < b.size(); i++) {
            b[i].min = simplify(b[i].min);
            b[i].max = simplify(b[i].max);
          }
        }

  // Helper function to merge the partial region map into the result region map.
        void merge_regions(map<string, Box> &result, const map<string, Box> &partial) {
      // Merge regions from 'partial' with an existing region in 'result'.
          for (const auto &reg : partial) {
            auto iter = result.find(reg.first);
            if (iter == result.end()) {
              result.emplace(reg.first, reg.second);
            } else {
              merge_boxes(iter->second, reg.second);
            }
          }
        }

  // Replace all occurrences of non-alphanumeric chars in 'name' with '_'.
        string get_sanitized_name(string name) {
          if (isdigit(name[0])) {
            name = "_" + name;
          }
          for (size_t i = 0; i < name.size(); ++i) {
            if (!isalnum(name[i])) {
              name[i] = '_';
            }
          }
          return name;
        }

        string get_expr_str(Expr expr){
          ostringstream ostr;
          ostr<<expr;
          string nst;
          nst=ostr.str();
          nst.erase(std::remove(nst.begin(), nst.end(), '"'), nst.end());
          return nst;

        }

        bool IsPowerOfTwo(Expr x)
        {
          return can_prove((x & (x - 1)) == 0);
        }


  // Representation of a function stage in the pipeline.
        struct FStage {
          Function func;
          uint32_t stage_num;
          FStage(Function func, uint32_t stage_num) : func(func), stage_num(stage_num) {}

          bool operator==(const FStage &other_stage) const {
            return (func.name() == other_stage.func.name()) &&
            (stage_num == other_stage.stage_num);
          }

          bool operator<(const FStage &other_stage) const {
            return func.name() < other_stage.func.name() ||
            ((func.name() == other_stage.func.name()) &&
              (stage_num < other_stage.stage_num));
          }

          friend std::ostream& operator<<(std::ostream &stream, const FStage &s) {
            if (s.stage_num == 0) {
              stream << s.func.name();
            } else {
              stream << s.func.name() << ".update(" << (s.stage_num - 1) << ")";
            }
            return stream;
          }
        };



        struct stage{
        public:
    //represent a stage
    // with vars
    // producing stages (which this consumes)
    // compute level
    // store level
    // reuse across each/which variable
          std::map <string,Expr> vars;
          std::vector<string> producers;
          pair<Expr,Expr> compute;
          pair<Expr,Expr> store;
          std::map <string,map<string,Expr>> re;
          bool is_input=1;
          bool output;
          string name;
          string statement;
          string costf;
          double cost;
          double rcost;
          std::vector<string> cols;
          double buffer;
          bool store_inter=false;
          bool compute_inter=false;
          bool is_inline;
          bool is_root;
          unsigned int stage_num=UINT_MAX;
          std::set<string> rvars;
          std::map<string,int> deps;
          std::map<string,int> fused_order={};
          std::map<string,int> var_order;
          std::map<string,int> strides;
          std::map<string,float> strided_access;



        };



        struct pipe_IR{

        public:
          std::map<string,stage> pipe;
          std::vector<FStage> pipe_f;
          std::map<string,Expr> tiles;
          std::map<string,Expr> bounds;
          string output_func;
          Expr total_cost;
          Expr wset;
          Expr wset_l2;
          std::map<string,Expr> intra_order;
          std::map<string,Expr> inter_order;
          bool store_inter;
          std::map<string,map<string,int>> stride_order;
          string col;
          map<string,Expr> min_tiles;
          void create_nest(){
            int ii=0;
            int io=0;

            for( auto it:pipe){

              if((it.second.output==1)||it.first==output_func){
                bool at_least_one=false;
                for(const auto its:it.second.vars){
                  if(can_prove(its.second>64)) at_least_one=true;
                }
                output_func=it.first;
            //    cout<<"it first "<<it.first<<endl;
                col=pipe[output_func].cols[0];
                for(auto its:it.second.vars){
          //        cout<<"VARVAR "<<its.first<<" ext "<<its.second<<endl;
                if(at_least_one){
                  if(((its.first==col)||
                    (can_prove(min_tiles[its.first]>0)&&(can_prove(its.second>min_tiles[its.first]))&&can_prove(its.second>64)))) {
                    tiles[its.first]=tile;
                  bounds[its.first]=its.second;
                  inter_order[its.first]=io++;
                  intra_order[its.first]=ii++;
                }else if (!can_prove(min_tiles[its.first]>0)){
            //     cout<<"var its-> "<<its.first<<" has no dep so outer"<<endl;
                  tiles[its.first]=its.second;
                  bounds[its.first]=its.second;
                  inter_order[its.first]=io++;
                }
                else{
                  tiles[its.first]=its.second;
                  bounds[its.first]=its.second;
                  intra_order[its.first]=ii++;
                }
              
            }
            else{
                if(((its.first==col)||
                    (can_prove(min_tiles[its.first]>0)&&(can_prove(its.second>min_tiles[its.first]))&&can_prove(its.second>0)))) {
                    tiles[its.first]=tile;
                  bounds[its.first]=its.second;
                  inter_order[its.first]=io++;
                  intra_order[its.first]=ii++;
                }else if (!can_prove(min_tiles[its.first]>0)){
           //       cout<<"var its-> "<<its.first<<" has no dep so outer non 2"<<endl;  
                  tiles[its.first]=its.second;
                  bounds[its.first]=its.second;
                  inter_order[its.first]=io++;
                }
                else{
                  tiles[its.first]=its.second;
                  bounds[its.first]=its.second;
                  intra_order[its.first]=ii++;
                }

            }
            }
          }
        }



    //check_strides();
    /*
    struct Group {
          // The output stage representing the group.
          FStage output;
          // Functions that belong to the group.
          vector<FStage> members;
          // Members of the group which are inlined.
          set<string> inlined;
          // Tile sizes along dimensions of the output function of the group.
          map<string, Expr> tile_sizes;

          Group(const FStage &output, const vector<FStage> &members)
              : output(output), members(members) {}
              */
        }


        void print_bufs(){
          for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
      //cout<<it->first<<" buffer "<<to_string(it->second.buffer)<<endl;
          }
        }

        void default_granularity(){
    //set all stages to root
          for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
            Expr root("root");
            it->second.compute_inter=false;
            it->second.store_inter=false;
     // root<<"root";
            it->second.compute.first=root;
            it->second.store.first=root;
            it->second.is_root=1;
            it->second.store.second=Expr();
            it->second.compute.second=Expr();
            if(!it->second.is_inline)  it->second.is_inline=0;
          }

        }





        void print_pipe(){
    //print pipe c/s
          cout<<"STAGES"<<endl;
          for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
            cout<<it->first<<endl<<"inline "<<it->second.is_inline<<endl;;
      //if(!store_inter){
            cout<<"Store: "<<it->second.store.first<<" "<<it->second.store.second<<" (inter) "<<it->second.store_inter<<endl;
            cout<<"Compute: "<<it->second.compute.first<<" "<<it->second.compute.second<<" (inter) "<<it->second.compute_inter<<endl<<endl;
    /*}else{
      cout<<"Store: "<<it->second.store[0]<<" "<<it->second.store[1]<<"o"<<endl;
      cout<<"Compute: "<<it->second.compute[0]<<" "<<it->second.compute[1]<<"o"<<endl<<endl;
    }*/
          }
          cout<<"LOOP"<<endl;
          for(auto it=tiles.begin();it!=tiles.end();++it){
            cout<<it->first<<" "<<it->second<<" "<<bounds[it->first]<<endl;
          }
          cout<<"Intra-tile Order"<<endl;
          for(auto it=intra_order.begin();it!=intra_order.end();++it){
            cout<<it->first<<" "<<it->second<<endl;
          }
          cout<<"Inter-tile Order"<<endl;
          for(auto it=inter_order.begin();it!=inter_order.end();++it){
            cout<<it->first<<" "<<it->second<<endl;
          }

    //cout<<endl<<endl<<"====================================="<<endl;
    /*for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
      if(it->second.compute[0]!="inline"){
        //cout<<it->first<<endl;
        for(std::map<string,int>::iterator ll=it->second.var_order.begin();ll!=it->second.var_order.end();++ll){
          //cout<<ll->first<<" "<<to_string(ll->second)<<endl;
        }
      }
    }*/
        //    for(auto it=pipe_f.begin();it!=pipe_f.end();++it){
       //       cout<<it->func.name()<<endl;
        //    }
    //cout<<pipe_f[pipe_f.size()-1].func.name()<<endl;
    //cout<<endl<<endl<<"====================================="<<endl;
  /*  //cout<<"FIXING ORDER"<<endl;
    for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
        for(std::map<string,int>::iterator its=it->second.strides.begin();its!=it->second.strides.end();++its){
        //cout<<its->first<<" "<<to_string(its->second)<<endl;
    }
    //cout<<"+++++++++++++++++++++++++++++++"<<endl;
    }*/

        }

        Expr find_var(std::map<string,Expr> m,Expr val){
   //   ////cout<<"LOOKING FOR VAR"<<std::endl;
          std::map<string,Expr>::iterator ll;
          for(ll=m.begin();ll!=m.end();++ll){
            if(!ll->second.defined())   continue;
            if(can_prove(ll->second==val))  {
     //     ////cout<<"found"<<std::endl;
              return ll->first;

            }
          }
    //#ifdef debug
    ////cout<<(val)<<" not found"<<endl;
    //#endif
          return Expr();
        } 


        void interchange(bool intra,vector<string> v1){
          if(!intra){
            for(uint i=0;i<v1.size();i++){
              string tmp="";
              tmp=v1[i];
              inter_order[tmp]=make_const(Int(32),i);
          ////cout<<tmp<<endl;
            }
          }else{
            for(uint i=0;i<v1.size();i++){
              string tmp="";
              tmp=v1[i];
          //if(tmp=="")   continue;
              intra_order[tmp]=make_const(Int(32),i);
          ////cout<<tmp<<endl;
            }
          }

        }

        void fill_stage(string name, std::map<string,Expr> vars, set<string> rvars, std::vector<string> producers, std::map<string,map<string,Expr>> re,std::vector<string> cols, bool out, FStage st,unsigned int st_num){
          pipe[name].vars=vars;
          pipe[name].producers=producers;
          pipe[name].re=re;
          pipe[name].output=out;
          pipe[name].cols=cols;
          pipe[name].name=name;
          pipe[name].rvars=rvars;
          pipe[name].stage_num=st_num;
          pipe_f.push_back(st);

        }



        void optimize_granularity(){

      //cout<<"fusion analysis..."<<endl;
          map<string,Expr> dumm_intra_order=intra_order;
      //Group stages
      //compute all at their consumers IFF there is reuse or consumed > 1 time
          for(auto its=pipe.begin();its!=pipe.end();++its){
            bool compute_inter=false;
            if(true){
              if(pipe.find(its->first)==pipe.end()) continue;
              if(its->first==output_func) continue;
              if(pipe[its->first].is_inline) continue;
              //#ifdef debug
         //     cout<<" PROD "<<its->first<<endl;
              //#endif
             // cout<<its->first<<endl;

             // bool check_next=false;
              //find its consumers - set storage 1 level above reuse (if any)
              for(auto it=pipe.begin();it!=pipe.end();++it){
            //    if(find(it->second.producers.begin(),it->second.producers.end(),its->first)==it->second.producers.end())  continue;
            //    if(it->first==its->first) continue;
                //  if(pipe[its->first].compute.second.defined()) check_next=true;
                if(it->second.re.size()!=0){
                   //   auto k=find(it->second.producers.begin(),it->second.producers.end(),its->first);
                   //   if(k!=it->second.producers.end()){

           //               cout<<"Cons "<<it->first<<endl;

                  pipe[its->first].is_root=false;
                  auto l=it->second.re.find(its->first);
                  if(l==it->second.re.end())  continue;
                          //find max order re;
                  std::pair<string,Expr> lk={"",make_const(Int(64),-1)};
                  for(auto ll=l->second.begin();ll!=l->second.end();++ll){

                    if((!ll->second.defined())||can_prove(ll->second==0))    continue;
            //         cout<<its->first<<" cons "<<it->first<<" overlap "<<ll->first<<" "<<ll->second<<" and bounds "<<bounds[ll->first]<<endl;
                    if(!dumm_intra_order[ll->first].defined()){
                      if(can_prove(lk.second==-1)){
                     Expr tmp=find_var(dumm_intra_order,make_zero(Int(32)));
                     ostringstream tmp_str;
                     tmp_str<<tmp;
                     lk.first=tmp_str.str();
                     lk.first.erase(std::remove(lk.first.begin(), lk.first.end(), '"'), lk.first.end());
                     lk.second=make_zero(Int(32));
                   }
                   }
                   else if(can_prove(intra_order[ll->first]>lk.second)){
                    lk.first=ll->first;
                    lk.second=intra_order[ll->first];
                  }
                }
                if(lk.first=="")   {
                  continue;
                }
                else pipe[its->first].is_inline=false;

                auto cv=dumm_intra_order.find(lk.first);
                //          cout<<"lk "<<lk.first<<endl;
                //          cout<<"cv "<<cv->first<<endl;
                bool is_col=find(it->second.cols.begin(),it->second.cols.end(),cv->first)!=it->second.cols.end();
                auto is_rdom=it->second.rvars.find(cv->first)!=it->second.rvars.end();
                Expr co=cv->second;
          //                cout<<" cv -> first "<<cv->first<<" 2nd "<<cv->second<<endl;
                Expr no=simplify(co+1);                       
          //                cout<<"c n "<<co<<" "<<no<<" intra size "<<dumm_intra_order.size()<<endl;
                Expr nv=find_var(dumm_intra_order,no);
                bool store_inter=false;
          //                  cout<<"nv "<<nv<<endl;
                 //         cout<<cv->first<<" "<<nv<<endl;
                if(nv.defined()){
                  string nv_str=get_expr_str(nv);
                    //          cout<<its->first<<" nv "<<nv_str<<" "<<it->second.cols[0]<<endl;
                  if(it->second.cols[0]==nv_str){
              //                    cout<<"no "<<no<<" nv b4 "<<nv_str<<" "<<it->second.cols[0]<<endl;
                    no=simplify(no+1);
                    nv=find_var(dumm_intra_order,no);
                //                  cout<<"no after "<<no<<" nv after "<<nv<<endl;
                  }
                }
                if(!nv.defined()){

                  nv=find_var(inter_order,make_zero(Int(64)));
                  store_inter=true;
            //      cout<<"nv not defined "<<nv<<endl;
                  pipe[its->first].store_inter=store_inter;  
                  pipe[its->first].store.second=nv;

                }                
                else if((!store_inter)&&(!pipe[its->first].store_inter)){
                  if(!pipe[its->first].store.second.defined()) {
                   pipe[its->first].store.second=nv;
              //     cout<<"its "<<its->first<<" store level "<<nv<<endl;
                 }
                 else{

                  string nst=get_expr_str(nv);
                  string ost=get_expr_str(pipe[its->first].store.second);

                  if(can_prove(dumm_intra_order[nst]>dumm_intra_order[ost])){
                    pipe[its->first].store.second=nv;
                  }

                }

              }

              string fr=get_expr_str(lk.first);

              Expr dep_lk=it->second.re[its->first][fr];

              if(!dep_lk.defined()) dep_lk=make_zero(Int(32));
              if(is_col||is_rdom||can_prove(dumm_intra_order[lk.first]<=dumm_intra_order[it->second.cols[0]])||(dep_lk.defined()&&bounds[fr].defined()&&can_prove(bounds[fr]<=dep_lk))){
                string new_var=get_expr_str(nv);
                if(!pipe[its->first].compute.second.defined()){ 
                  pipe[its->first].compute.second=nv;
            //        cout<<"compute was moved to nv "<<nv<<" because is_rdom"<<is_rdom<<" is col "<<is_col<<endl;
                  if((pipe[its->first].store_inter)&&(bounds[fr].defined()&&can_prove(bounds[fr]<=dep_lk))) {
                    compute_inter=1;
                         //                        cout<<"compute "<<its->first<<" inter"<<endl;
                  }
                  else if(can_prove(dumm_intra_order[lk.first]>dumm_intra_order[new_var])) compute_inter=1;
                }
                else{

                  string ncp=get_expr_str(nv);

                  string ocp=get_expr_str(pipe[its->first].compute.second);
                                  //ocp=old_compute_level.str();
                                  //ocp.erase(std::remove(ocp.begin(), ocp.end(), '"'), ocp.end());
                                  //cout<<its->first<<" "<<ocp<<" "<<ncp<<endl;
                  if(can_prove(dumm_intra_order[ncp]>dumm_intra_order[ocp])){
                    pipe[its->first].compute.second=nv;
                    if(!dep_lk.defined()) dep_lk=make_zero(Int(32));
                    if((pipe[its->first].store_inter)&&bounds[fr].defined()&&can_prove(bounds[fr]<=dep_lk)){
                      compute_inter=1;
                                          //cout<<"compute "<<its->first<<" inter"<<endl;
                    }   
                  }  
                }
              }
              else{
                if(!pipe[its->first].compute.second.defined())    pipe[its->first].compute.second=lk.first;  
                else{
                                  //ostringstream old_compute_level;
                                  //old_compute_level<<pipe[its->first].compute.second;
                                  //ostringstream new_compute_level;
                                  //new_compute_level<<lk.first;
                  string ncp=get_expr_str(lk.first);
                  string ocp=get_expr_str(pipe[its->first].compute.second);
                                  //ncp=new_compute_level.str();
                                  //ocp=old_compute_level.str();
                                  //ncp.erase(std::remove(ncp.begin(), ncp.end(), '"'), ncp.end());
                                  //ocp.erase(std::remove(ocp.begin(), ocp.end(), '"'), ocp.end());
                                  //cout<<its->first<<" "<<ocp<<" "<<ncp<<endl;
                  if(can_prove(dumm_intra_order[ncp]>dumm_intra_order[ocp])){
                    pipe[its->first].compute.second=lk.first;
                  }
                }


              }

            }
          }
        }
        pipe[its->first].compute_inter=compute_inter;
        Function f;
          //sint n_st=0;
        for(const auto &qq:pipe_f){
          if(qq.func.name()==its->first){
            f=qq.func;
            // n_st=qq.stage_num;
            //  break;
          }
        }

          //if(!pipe[its->first].compute.second.defined()||(is_func_trivial_to_inline_mem(f)))  pipe[its->first].is_inline=true;
      //  if(its->first=="bokeh_radius_squared")  pipe[its->first].is_inline=true;

        if(!pipe[its->first].compute.second.defined()) {
         if(!f.can_be_inlined()){
          cout<<its->first<<" SHOULDNT BE INLINED"<<endl;
          while(true);
        }
       // cout<<its->first<<" is inlined\n";
        if(its->first!=output_func)  pipe[its->first].is_inline=true;
      }
    }


    for(std::map<string, stage>::iterator its=pipe.begin();its!=pipe.end();++its){
      if(true){
        ostringstream clevel;
        clevel<<pipe[its->first].compute.first;
        if((!pipe[its->first].is_root)&&(!pipe[its->first].is_inline)&&(clevel.str()!=output_func)){
          pipe[its->first].compute.first=output_func;
          pipe[its->first].store.first=output_func;
        }

      }
    }

    bool ch_flag;
    do{
      ch_flag=false;
          //make sure that compute/store level of producers is equal or higher than the consuming stages
      for(std::map<string, stage>::iterator its=pipe.begin();its!=pipe.end();++its){
        if(true){
          if(pipe[its->first].compute_inter)  continue;
              //find its consumers
          for(std::map<string,stage>::iterator it=pipe.begin();it!=pipe.end();++it){
            if(it->second.re.size()!=0){
              std::vector<string>::iterator k;
              k=find(it->second.producers.begin(),it->second.producers.end(),its->first);
              if(k!=it->second.producers.end()){
                if((!it->second.is_root)&&(!it->second.is_inline)){
                  Expr cl1=pipe[its->first].compute.second;
                  Expr sl1=pipe[its->first].store.second;
                  Expr cl2=it->second.compute.second;
                                  /*ostringstream c_lp,s_lp,c_lc;
                                  c_lp<<cl1;
                                  s_lp<<sl1;
                                  c_lc<<cl2;*/
                  string clp=get_expr_str(cl1);
                  string slp=get_expr_str(sl1);
                  string clc=get_expr_str(cl2);
                                  //string slp=s_lp.str();
                                  //string clc=c_lc.str();

                                  //clp.erase(std::remove(clp.begin(), clp.end(), '"'), clp.end());
                                  //slp.erase(std::remove(slp.begin(), slp.end(), '"'), slp.end());
                                  //clc.erase(std::remove(clc.begin(), clc.end(), '"'), clc.end());
                  if(!sl1.defined())  continue;
                  if(!cl1.defined())  continue;
                  if(!cl2.defined())  continue;
                  if(can_prove(dumm_intra_order[clp]<dumm_intra_order[clc])||it->second.compute_inter){
                    if(it->second.compute_inter)  {
                      pipe[its->first].compute_inter=true;
          //                                cout<<"CHANGING in "<<its->first<<" compute at to inter"<<endl;
                    }
            //                          cout<<"CHANGING  in "<<its->first<<" compute at "<<clp<<" to "<<clc<<endl;
                    pipe[its->first].compute.second=it->second.compute.second;
                    if(can_prove(dumm_intra_order[slp]<dumm_intra_order[clc])){
              //                            cout<<"CHANGING  in "<<its->first<<" store at "<<clp<<" to "<<clc<<endl;
                      pipe[its->first].store.second=it->second.compute.second;
                    }
                  }

                }
                                  //if((it->second.compute[0]!=pipe[its->first].compute[0])){
                                  //pipe[its->first].compute[0]=it->second.compute[0];
                                  //pipe[its->first].store[0]=it->second.store[0];
                                  //ch_flag=true;
                                  //if(pipe[its->first].store[1]==""){
                                  //    pipe[its->first].store[1]=it->second.store[1];
                                  //    ////cout<<"compute"<<it->second.store[1];

  //                                }
              }


            }
          }
        }
      }

    }while(ch_flag);
   //   cout<<"AFTER"<<endl;
   //   print_pipe();

      //////cout<<"DONE"<<std::endl;
  }


  };






  // Check if all the pipeline outputs have estimates specified
  // on each of their dimensions; otherwise, throw an assertion.
  void check_estimates_on_outputs(const vector<Function> &outputs) {
    for (const auto &out : outputs) {
      const vector<Bound> &estimates = out.schedule().estimates();
          // Check if the estimate for each dimension of the output is available
          // and is an integer. If there are duplicates for the estimate of a
          // dimension, we only check the last defined estimate (which min and
          // extent values are defined) since it is the one that would be
          // eventually used.
      Bound est;
      for (const auto &arg : out.args()) {
        bool found = false;
        for (int i = (int)estimates.size() - 1; i >= 0; --i) {
          if ((estimates[i].var == arg) && estimates[i].min.defined() &&
            estimates[i].extent.defined()) {
            found = true;
          est = estimates[i];
          break;
        }
      }
      user_assert(found && est.min.type().is_int() && est.extent.type().is_int())
      << "Please provide a valid estimate for dimension "
      << est.var << " of output \"" << out.name() << "\"\n";
    }
  }
  }










  struct DependenceAnalysis {
      // Map containing all the functions in the pipeline.        
    map<string, Function> env;
    vector<string> order;
    FuncValueBounds func_val_bounds;

    struct RegionsRequiredQuery {
      string f;
      int stage;
      set<string> prods;
      bool only_regions_computed;

      RegionsRequiredQuery(const string &f, int stage, const set<string> &prods,
       bool only_regions_computed)
      : f(f), stage(stage), prods(prods),
      only_regions_computed(only_regions_computed) {}

      bool operator==(const RegionsRequiredQuery &other) const {
        return (f == other.f) && (stage == other.stage) && (prods == other.prods) &&
        (only_regions_computed == other.only_regions_computed);
      }
      bool operator<(const RegionsRequiredQuery &other) const {
        if (f < other.f) {
          return true;
        } else if (f > other.f) {
          return false;
        }
        if (stage < other.stage) {
          return true;
        } else if (stage > other.stage) {
          return false;
        }
        if (only_regions_computed < other.only_regions_computed) {
          return true;
        } else if (only_regions_computed > other.only_regions_computed) {
          return false;
        }
        return prods < other.prods;
      }
    };
    struct RegionsRequired {
      DimBounds bounds;
          // Regions required to compute 'bounds' given a particular
          // RegionsRequiredQuery.
      map<string, Box> regions;
      RegionsRequired(const DimBounds &b, const map<string, Box> &r)
      : bounds(b), regions(r) {}
    };
      // Cache for bounds queries (bound queries with the same parameters are
      // common during the grouping process).
    map<RegionsRequiredQuery, vector<RegionsRequired>> regions_required_cache;

    DependenceAnalysis(const map<string, Function> &env, const vector<string> &order,
     const FuncValueBounds &func_val_bounds)
    : env(env), order(order), func_val_bounds(func_val_bounds) {}

      // Return the regions of the producers ('prods') required to compute the region
      // of the function stage ('f', 'stage_num') specified by 'bounds'. When
      // 'only_regions_computed' is set to true, this only returns the computed
      // regions and not the total allocated regions.
    map<string, Box> regions_required(Function f, int stage_num,
      const DimBounds &bounds,
      const set<string> &prods,
      bool only_regions_computed,
      const Scope<Interval> *input_estimates);

      // Return the regions of the producers ('prods') required to compute the region
      // of the function specified by 'pure_bounds'. When 'only_regions_computed'
      // is set to true, this only returns the computed regions and not the total
      // allocated regions.
    map<string, Box> regions_required(Function f,
      const DimBounds &pure_bounds,
      const set<string> &prods,
      bool only_regions_computed,
      const Scope<Interval> *input_estimates);

      // Return redundantly computed regions of producers ('prods') while computing
      // a region of the function stage ('f', 'stage_num') specified by 'bounds'.
      // 'var' is the dimension along which redundant computation is accounted for.
      // When 'only_regions_computed' is set to true, this only returns the computed
      // regions and not the total allocated regions. When 'only_regions_computed'
      // is set to true, this only returns the computed regions and not the total
      // allocated regions.
    map<string, Box> redundant_regions(Function f, int stage_num, string var,
     const DimBounds &bounds,
     const set<string> &prods,
     bool only_regions_computed,
     const Scope<Interval> *input_estimates);

      // Return overlapping regions of producers ('prods') while computing a function
      // stage along each of the dimensions.
    vector<map<string, Box>>
    overlap_regions(Function f, int stage_num, const DimBounds &bounds,
      const set<string> &prods, bool only_regions_computed,
      const Scope<Interval> *input_estimates);
  };

  // Return the regions of the producers ('prods') required to compute the region
  // of the function specified by 'pure_bounds'.
  map<string, Box>
  DependenceAnalysis::regions_required(Function f, const DimBounds &pure_bounds,
   const set<string> &prods,
   bool only_regions_computed,
   const Scope<Interval> *input_estimates) {
      // Find the regions required for each stage and merge them.
    map<string, Box> regions;
    int num_stages = f.updates().size() + 1;
    for (int s = 0; s < num_stages; s++) {
      DimBounds bounds = get_stage_bounds(f, s, pure_bounds);
      map<string, Box> stage_regions =
      regions_required(f, s, bounds, prods, only_regions_computed, input_estimates);

      merge_regions(regions, stage_regions);
    }
    return regions;
  }

  struct StageBounds {
    FStage f_stage;
    DimBounds bounds;

    StageBounds(const FStage &fs, const DimBounds &b) : f_stage(fs), bounds(b) {}
    StageBounds(Function func, uint32_t stage_num, const DimBounds &b) :
    f_stage(FStage(func, stage_num)), bounds(b) {}

    bool operator==(const StageBounds &other) const {
      return (f_stage == other.f_stage) && (bounds == other.bounds);
    }
    bool operator<(const StageBounds &other) const {
      return (f_stage < other.f_stage) ||
      ((f_stage == other.f_stage) && (bounds.size() < other.bounds.size()));
    }
    friend std::ostream& operator<<(std::ostream &stream, const StageBounds &s) {
      stream << "Stage: " << s.f_stage << "\n";
      stream << "Bounds:\n";
      for (const auto &iter : s.bounds) {
        stream << "\t" << iter.first << " -> [" << iter.second.min << ", " << iter.second.max << "]\n";
      }
      stream << "\n";
      return stream;
    }
  };

  // Helper function to queue regions that need to be traversed. 'fs_bounds' is
  // the queue into which the regions specified by 'prod_func' and 'region'
  // will be added.
  void queue_func_regions(map<FStage, DimBounds> &fs_bounds,
    const Function &prod_func, const Box &region,
    const set<StageBounds>& visited) {
    DimBounds prod_pure_bounds;
    const vector<string> &args = prod_func.args();

    internal_assert(region.size() == args.size());

      // The region only specifies the extent of each dimension
      // by position. Populating a map which is keyed by name.
    for (size_t v = 0; v < args.size(); v++) {
      prod_pure_bounds[args[v]] = region[v];
    }

      // Get the bounds of all stages in a function from the
      // bounds on the pure dimensions.
    vector<DimBounds> prod_bounds = get_stage_bounds(prod_func, prod_pure_bounds);

    size_t num_stages = prod_func.updates().size() + 1;

    internal_assert(prod_bounds.size() == num_stages);

      // Add all stages of a function into the queue.
    for (size_t prod_s = 0; prod_s < num_stages; prod_s++) {
      StageBounds sb(prod_func, prod_s, prod_bounds[prod_s]);
      if (visited.find(sb) == visited.end()) {
        auto iter = fs_bounds.find(sb.f_stage);
        if (iter == fs_bounds.end()) {
          fs_bounds.emplace(sb.f_stage, sb.bounds);
        } else {
          for (const auto &b : sb.bounds) {
            DimBounds &curr_bounds = iter->second;
            auto b_iter = curr_bounds.find(b.first);
            if (b_iter == curr_bounds.end()) {
              curr_bounds.emplace(b.first, b.second);
            } else {
              if (b_iter->second.has_lower_bound() && b.second.has_lower_bound()) {
                b_iter->second.min = simplify(Interval::make_min(b_iter->second.min, b.second.min));
              } else {
                b_iter->second.min = Interval::neg_inf;
              }

              if (b_iter->second.has_upper_bound() && b.second.has_upper_bound()) {
                b_iter->second.max = simplify(Interval::make_max(b_iter->second.max, b.second.max));
              } else {
                b_iter->second.max = Interval::pos_inf;
              }
            }
          }
        }
      }
    }
  }

  // Helper function for merging 'curr_regions' to the global map of regions
  // and adding them to the queue of regions that need to be traversed.
  // 'prods' is the set of producer functions that are under consideration.
  void merge_and_queue_regions(map<FStage, DimBounds> &fs_bounds,
   map<string, Box> &regions,
   map<string, Box> &curr_regions,
   const set<string> &prods,
   const map<string, Function> &env,
   bool only_regions_computed,
   string curr_func_name,
   const set<StageBounds>& visited) {
    for (const auto &reg : curr_regions) {
          // Merge region with an existing region of a function in the
          // global map. Do not merge the parent function itself to the region
          // when querying only for the values computed.
      if (!only_regions_computed || (only_regions_computed && (reg.first != curr_func_name))) {
        auto iter = regions.find(reg.first);
        if (iter == regions.end()) {
          regions.emplace(reg.first, reg.second);
        } else {
          merge_boxes(iter->second, reg.second);
        }
      }

          // Skip adding the current region into to the queue if the function
          // is not in 'prods'.
      if (prods.find(reg.first) == prods.end()) {
        continue;
      }

      const auto &it = env.find(reg.first);
      if ((it != env.end()) && (reg.first != curr_func_name)) {
              // Add all stages of the function representing the
              // region into the queue.
        queue_func_regions(fs_bounds, it->second, reg.second, visited);
      }
    }
  }

  // Return the regions of the producers ('prods') required to compute the region
  // of the function stage ('f', 'stage_num') specified by 'bounds'.
  map<string, Box>
  DependenceAnalysis::regions_required(Function f, int stage_num,
   const DimBounds &bounds,
   const set<string> &prods,
   bool only_regions_computed,
   const Scope<Interval> *input_estimates) {
      // Iteratively compute the required regions by traversing the chain
      // of dependencies.

      // Check the cache if we've already computed this previously.
    RegionsRequiredQuery query(f.name(), stage_num, prods, only_regions_computed);
    const auto &iter = regions_required_cache.find(query);
    if (iter != regions_required_cache.end()) {
      const auto &it = std::find_if(iter->second.begin(), iter->second.end(),
        [&bounds](const RegionsRequired &r) { return (r.bounds == bounds); });
      if (it != iter->second.end()) {
        internal_assert((iter->first == query) && (it->bounds == bounds));
        return it->regions;
      }
    }

      // Map of all the required regions.
    map<string, Box> regions;
    map<FStage, DimBounds> fs_bounds;
    set<StageBounds> visited;

      // Add the query function and its region to the queue.
    fs_bounds.emplace(FStage(f, stage_num), bounds);

    while (!fs_bounds.empty()) {
      for (int i = order.size() - 1; i >= 0; --i) {
        const Function &f = env.find(order[i])->second;
        int num_stages = f.updates().size() + 1;
        for (int stage_num = 0; stage_num < num_stages; ++stage_num) {
          FStage s(f, stage_num);

          const auto &iter = fs_bounds.find(s);
          if (iter == fs_bounds.end()) {
            continue;
          }

          DimBounds curr_bounds = iter->second;
          visited.insert(StageBounds(s, curr_bounds));

                  // Scope for containing all the estimates on parameters and intervals.
          Scope<Interval> curr_scope;
          curr_scope.set_containing_scope(input_estimates);

                  // If the function has an extern definition, there is no visibility into
                  // the expression defining the function. So the regions required will be
                  // the entire domain of the inputs to the extern func. Use the estimates
                  // on the inputs to the extern function if available.
                  //
                  // TODO: Query the extern function for bounds of the functions which it
                  // it depends on. This can be done by calling the extern func in the
                  // bounds query mode.
          if (s.func.has_extern_definition()) {
            for (const ExternFuncArgument &arg : s.func.extern_arguments()) {
              if (arg.is_func()) {
                              // If the argument is an entire function, the bounds of the
                              // function required are unknown. Create an infinite region
                              // of the correct dimension, update the region map, and
                              // add it to the queue.
                string prod_name = Function(arg.func).name();
                const Function &prod_func = get_element(env, prod_name);
                map<string, Box> prod_reg;
                const vector<string> &args = prod_func.args();
                for (size_t v = 0; v < args.size(); v++) {
                  prod_reg[prod_name].push_back(Interval());
                }
                merge_and_queue_regions(fs_bounds, regions, prod_reg, prods, env,
                  only_regions_computed, s.func.name(), visited);
              } else if (arg.is_expr()) {
                              // Find the boxes required for the expression and add the regions
                              // to the queue.
                Expr subs_arg = subsitute_var_estimates(arg.expr);
                map<string, Box> arg_regions = boxes_required(subs_arg, curr_scope, func_val_bounds);
                substitute_estimates_region(arg_regions);
                merge_and_queue_regions(fs_bounds, regions, arg_regions, prods, env,
                  only_regions_computed, s.func.name(), visited);
              } else if (arg.is_image_param() || arg.is_buffer()) {
                              // If the argument is an image or a buffer, the required
                              // bounds are unknown. Create an infinite region of the
                              // correct dimension and update the region map.
                Buffer<> buf;
                if (arg.is_image_param()) {
                  buf = arg.image_param.buffer();
                } else {
                  buf = arg.buffer;
                }
                map<string, Box> buf_reg;
                for (int v = 0; v < buf.dimensions(); v++) {
                  buf_reg[buf.name()].push_back(Interval());
                }
                merge_regions(regions, buf_reg);
              }
            }
          } else {
            Definition def = get_stage_definition(s.func, s.stage_num);
            const vector<Dim> &dims = def.schedule().dims();

                      // Substitute parameter estimates into the bounds and add them to the
                      // current scope.
            for (int d = 0; d < (int)dims.size() - 1; d++) {
              Interval simple_bounds = get_element(curr_bounds, dims[d].var);
              simple_bounds.min = subsitute_var_estimates(simple_bounds.min);
              simple_bounds.max = subsitute_var_estimates(simple_bounds.max);
              curr_scope.push(dims[d].var, simple_bounds);
            }

                      // Find the regions required for each value of the current function stage,
                      // update the region map, and add them to the queue.
            for (const auto &val : def.values()) {
                          // Substitute the parameter estimates into the expression and get
                          // the regions required for the expression.
              Expr subs_val = subsitute_var_estimates(val);
              map<string, Box> curr_regions = boxes_required(subs_val, curr_scope, func_val_bounds);
              substitute_estimates_region(curr_regions);

                          // Arguments to the definition may require regions of functions.
                          // For example, update definitions in histograms where the bin is
                          // based on the value of a function.
              Box left_reg;
              for (const Expr &arg : def.args()) {
                Expr subs_arg = subsitute_var_estimates(arg);
                map<string, Box> arg_regions = boxes_required(subs_arg, curr_scope, func_val_bounds);
                substitute_estimates_region(arg_regions);

                              // Merge the regions with the regions found while looking at
                              // the values.
                merge_regions(curr_regions, arg_regions);

                Interval arg_bounds = bounds_of_expr_in_scope(arg, curr_scope, func_val_bounds);
                left_reg.push_back(arg_bounds);
              }

              auto iter_curr = curr_regions.find(s.func.name());
              if (iter_curr == curr_regions.end()) {
                curr_regions.emplace(s.func.name(), left_reg);
              } else {
                merge_boxes(iter_curr->second, left_reg);
              }

                          // Update the region map, and add 'curr_regions' to the queue.
              merge_and_queue_regions(fs_bounds, regions, curr_regions, prods, env,
                only_regions_computed, s.func.name(), visited);
            }
          }

                  // Remove processed region from the queue.
          fs_bounds.erase(iter);
        }
      }
    }

      // Simplify the bounds on each region and substitute global pipeline
      // bounds for function regions which lower and upper bounds could not be
      // determined.
    map<string, Box> concrete_regions;

    for (auto &f_reg : regions) {
      simplify_box(f_reg.second);

      Box concrete_box;
      for (size_t i = 0; i < f_reg.second.size(); i++) {
        Expr lower = f_reg.second[i].min;
        Expr upper = f_reg.second[i].max;

        auto iter = env.find(f_reg.first);
        bool in_env = (iter != env.end());


        if (!lower.as<IntImm>() && in_env) {
          const Function &curr_f = iter->second;
          for (const auto &b : curr_f.schedule().estimates()) {
            size_t num_pure_args = curr_f.args().size();
            if ((i < num_pure_args) && (b.var == curr_f.args()[i])) {
              lower = b.min;
            }
          }
        }

        if (!upper.as<IntImm>() && in_env) {
          const Function &curr_f = iter->second;
          for (const auto &b : curr_f.schedule().estimates()) {
            size_t num_pure_args = curr_f.args().size();
            if ((i < num_pure_args) && (b.var == curr_f.args()[i])) {
              const IntImm *bmin = b.min.as<IntImm>();
              const IntImm *bextent = b.extent.as<IntImm>();
              upper = IntImm::make(Int(32), bmin->value + bextent->value - 1);
            }
          }
        }

        Interval concrete_bounds = Interval(lower, upper);
        concrete_box.push_back(concrete_bounds);
      }
      concrete_regions[f_reg.first] = concrete_box;
    }

    regions_required_cache[query].push_back(RegionsRequired(bounds, concrete_regions));
    return concrete_regions;
  }

  // Return redundantly computed regions of producers ('prods') while computing a
  // region of the function stage ('f', 'stage_num') specified by 'bounds'. 'var'
  // is the dimension along which redundant computation is accounted for.
  map<string, Box>
  DependenceAnalysis::redundant_regions(Function f, int stage_num, string var,
    const DimBounds &bounds,
    const set<string> &prods,
    bool only_regions_computed,
    const Scope<Interval> *input_estimates) {
      // Find the regions required to compute the region of 'f' specified
      // by 'bounds'.
    map<string, Box> regions = regions_required(
      f, stage_num, bounds, prods, only_regions_computed, input_estimates);

      // Shift the bounds by the size of the interval along the direction
      // of var.
    DimBounds shifted_bounds;

    for (const auto &b : bounds) {
      if (b.first == var) {
        Expr len = b.second.max - b.second.min + 1;
        Interval bound = Interval(b.second.min + len, b.second.max + len);
        shifted_bounds[b.first] = bound;
      } else {
        shifted_bounds[b.first] = b.second;
      }
    }

      // Find the regions required to compute the region of f specified
      // by shifted_bounds.
    map<string, Box> regions_shifted = regions_required(
      f, stage_num, shifted_bounds, prods, only_regions_computed, input_estimates);

      // Compute the overlaps between 'regions_shifted' and the original
      // regions required.
    map<string, Box> overlaps;
    for (const auto &reg : regions) {
      auto iter = regions_shifted.find(reg.first);
      if (iter == regions.end()) {
              // It will be interesting to log cases where this actually happens
              // i.e., the shifted regions do not contain a function that was
              // there in the original regions.
        continue;
      }
      const Box &b = reg.second;
      const Box &b_shifted = iter->second;
          // The boxes should be of the same size.
      internal_assert(b.size() == b_shifted.size());

      Box b_intersect;
      for (uint32_t i = 0 ; i < b.size(); i++) {
        b_intersect.push_back(Interval::make_intersection(b[i], b_shifted[i]));
      }
          // A function should appear once in the regions and therefore cannot
          // already be present in the overlaps map.
      internal_assert(overlaps.find(reg.first) == overlaps.end());
      overlaps.emplace(reg.first, b_intersect);
    }

      // Simplify the bounds of each of the overlap regions.
    for (auto &f : overlaps) {
      simplify_box(f.second);
    }

    return overlaps;
  }

  // Return overlapping regions of producers ('prods') while computing a function
  // stage along each of the dimensions.
  vector<map<string, Box>>
  DependenceAnalysis::overlap_regions(Function f, int stage_num,
    const DimBounds &bounds,
    const set<string> &prods,
    bool only_regions_computed,
    const Scope<Interval> *input_estimates) {
    vector<map<string, Box>> conc_overlaps;

    const vector<Dim> &dims = get_stage_dims(f, stage_num);

      // Get the redundant regions along each dimension of f.
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      map<string, Box> conc_reg = redundant_regions(f, stage_num, dims[d].var, bounds,
        prods, only_regions_computed, input_estimates);
      conc_overlaps.push_back(conc_reg);
    }
    return conc_overlaps;
  }

  // Return the regions of each function required for computing the
  // outputs of the pipeline.
  map<string, Box> get_pipeline_bounds(DependenceAnalysis &analysis,
   const vector<Function> &outputs,
   const Scope<Interval> *input_estimates) {
    map<string, Box> pipeline_bounds;

      // Find the regions required for each of the outputs and merge them
      // to compute the full pipeline_bounds.
    for (const auto &out : outputs) {
      DimBounds pure_bounds;
      Box out_box;
          // Use the estimates on the output for determining the output bounds.
          // If there are duplicates, use the most recent estimate.
      const auto &estimates = out.schedule().estimates();
      for (const auto &arg : out.args()) {
        int i;
        for (i = estimates.size() - 1; i >= 0; --i) {
          const auto &est = estimates[i];
          if ((est.var == arg) && est.min.defined() && est.extent.defined()) {
            Interval in = Interval(est.min, simplify(est.min + est.extent - 1));
            pure_bounds.emplace(arg, in);
            out_box.push_back(in);
            break;
          }
        }
        internal_assert(i >= 0) << "Could not find estimate for " << arg << "\n";
      }

      set<string> prods;
      for (const pair<string, Function> &fpair : analysis.env) {
        prods.insert(fpair.first);
      }

      map<string, Box> regions = analysis.regions_required(out, pure_bounds, prods,
       false, input_estimates);

          // Add the output region to the pipeline bounds as well.
      regions.emplace(out.name(), out_box);

      merge_regions(pipeline_bounds, regions);
    }

    return pipeline_bounds;
  }

  struct AutoSchedule {
    struct Stage {
      string function;
      size_t stage;

      Stage(const string &f, size_t s) : function(f), stage(s) {}

      bool operator==(const Stage &other) const {
        return (function == other.function) && (stage == other.stage);
      }
      bool operator<(const Stage &other) const {
        return (function < other.function) || ((function == other.function) && (stage < other.stage));
      }
    };

    const map<string, Function> &env;

      // Contain maps from function name to the topological order of the pipeline.
    map<string, size_t> topological_order;

      // Cache for storing all internal vars/rvars that have been declared during
      // the course of schedule generation, to ensure that we don't introduce any
      // duplicates in the string representation of the schedules.
    map<string, VarOrRVar> internal_vars;

      // Store the list of schedules applied to some function stages (most recent
      // schedule is placed last in the list).
    map<string, map<int, vector<string>>> func_schedules;

      // Store the list of vars/rvars used in the schedule applied to some
      // function stages.
    map<string, map<int, set<string>>> used_vars;

    AutoSchedule(const map<string, Function> &env, const vector<string> &order) : env(env) {
      for (size_t i = 0; i < order.size(); ++i) {
        topological_order.emplace(order[i], i);
      }
          // Allocate a slot in 'used_vars' for each function stages in the pipeline
      for (const auto &iter : env) {
        for (size_t i = 0; i < iter.second.updates().size() + 1; ++i) {
          used_vars[iter.first][i];
        }
      }
    }

      // Given a function name, return a string representation of getting the
      // function handle
    string get_func_handle(const string &name) const {
      size_t index = get_element(topological_order, name);
      return "pipeline.get_func(" + std::to_string(index) + ")";
    }

    friend std::ostream& operator<<(std::ostream &stream, const AutoSchedule &sched) {
      stream << "// Delete this line if not using Generator\n";
      stream << "Pipeline pipeline = get_pipeline();\n\n";

      for (const auto &iter : sched.internal_vars) {
        if (iter.second.is_rvar) {
          stream << "RVar ";
        } else {
          stream << "Var ";
        }
        stream << iter.first << "(\"" << iter.first << "\");\n";
      }
      stream << "\n";

          // Declare all the functions + schedules
      std::ostringstream func_ss;
      std::ostringstream schedule_ss;

      for (const auto &f : sched.func_schedules) {
        const string &fname = get_sanitized_name(f.first);
        func_ss << "Func " << fname << " = " << sched.get_func_handle(f.first) << ";\n";

        schedule_ss << "{\n";

              // Declare all the Vars and RVars that are actually used in the schedule
        const Function &func = get_element(sched.env, f.first);
        for (size_t i = 0; i < func.args().size(); ++i) {
          if (sched.used_vars.at(func.name()).at(0).find(func.args()[i])
            != sched.used_vars.at(func.name()).at(0).end()) {
            schedule_ss << "    Var " << func.args()[i] << " = "
          << fname << ".args()[" << i << "];\n";
        }
      }
      set<string> declared_rvars;
      for (size_t i = 0; i < func.updates().size(); ++i) {
        const vector<ReductionVariable> &rvars = func.updates()[i].schedule().rvars();
        const set<string> &var_list = sched.used_vars.at(func.name()).at(i+1);
        for (size_t j = 0; j < rvars.size(); ++j) {
          if ((var_list.find(rvars[j].var) == var_list.end()) ||
            (declared_rvars.find(rvars[j].var) != declared_rvars.end())) {
            continue;
        }
        declared_rvars.insert(rvars[j].var);
        schedule_ss << "    RVar " << rvars[j].var << "("
        << fname << ".update(" << i << ").get_schedule().rvars()[" << j << "].var);\n";
      }
    }

    for (const auto &s : f.second) {
      internal_assert(!s.second.empty());
      schedule_ss << "    " << fname;
      if (s.first > 0) {
        schedule_ss << ".update(" << std::to_string(s.first - 1) << ")";
      }
      for (size_t i = 0; i < s.second.size(); ++i) {
        schedule_ss << "\n        ." << s.second[i];
      }
      schedule_ss << ";\n";
    }

    schedule_ss << "}\n";
  }

  stream << func_ss.str() << "\n";
  stream << schedule_ss.str() << "\n";

  return stream;
  }

  void push_schedule(const string &stage_name, size_t stage_num,
   const string &sched, const set<string> &vars) {
    vector<string> v = split_string(stage_name, ".");
    internal_assert(!v.empty());

    used_vars[v[0]][stage_num].insert(vars.begin(), vars.end());

          // If the previous schedule applied is the same as this one,
          // there is no need to re-apply the schedule
    auto &schedules = func_schedules[v[0]][stage_num];
    if (schedules.empty()) {
      schedules.push_back(sched);
    } else {
      if (schedules[schedules.size()-1] != sched) {
        schedules.push_back(sched);
      }
    }
  }
  };

  // Implement the grouping algorithm and the cost model for making the grouping
  // choices.
  struct Partitioner {
      // GroupingChoice encodes the grouping of the 'prod' function into the 'cons' stage.
    struct GroupingChoice {
      string prod;
      FStage cons;

      GroupingChoice(const string &prod, const FStage &cons) : prod(prod), cons(cons) {}

      bool operator==(const GroupingChoice &other) const {
        return (prod == other.prod) && (cons == other.cons);
      }

      bool operator<(const GroupingChoice &other) const {
        return (prod < other.prod) || ((prod == other.prod) && (cons < other.cons));
      }

      friend std::ostream& operator<<(std::ostream &stream, const GroupingChoice &choice) {
        stream << "Choice: " << choice.prod << " -> " << choice.cons << '\n';
        return stream;
      }
    };

      // A group is a sub-pipeline with a single output. Members of a group are
      // either inlined into the consumer functions within the group or computed
      // at tiles of the output, specified by 'tile_sizes'.
      //
      // TODO: The restriction of computing either at the inline or tile level
      // makes the space of scheduling choices for a group very tractable.
      // However, the restriction might miss good schedules which can only be
      // realized by computing the members of the group at different levels of
      // the group.
      //
      // There are two approaches to extend the space of schedules considered:
      // 1) Recursive grouping: Treat the problem of determining the compute levels
      // within a group as a smaller instance of the grouping problem with
      // different parameters for the input, output sizes, and cache model.
      //
      // 2) Tightening: Always compute a function at the lowest level possible
      // without introducing redundant work. This is a restricted form of recursive
      // grouping which does not explore the trade-off between redundant work and
      // locality.
      //
      // Either approach can be implemented as a post process for each group
      // after the initial grouping process finishes. The cost model may
      // already make sub-optimal higher level partitioning when it is not aware
      // of the benefits of the post processing. However, it should strictly be
      // an improvement over the initial grouping. As a first step, it is good
      // to make it a post process.
      //
      // Incorporating the recursive grouping process into the cost model can be
      // tricky and can potentially make the cost of analyzing a group
      // prohibitive, as it requires solving smaller instances of the grouping
      // problem for analyzing each configuration. On the other hand, tightening
      // can be integrated into the cost model with out significantly increasing
      // the time to analyze a grouping configuration.
      //
      // TODO: Add sliding window optimizations. For start, it may be enough to
      // implement sliding window as a post-pass by moving the store level of all
      // the members of the group to the outermost serial loop. This could possibly
      // be incorporated in the cost model with some effort. Line-buffering
      // presents additional challenges for this post-processing strategy though.
      // A typical line-buffer would use terrible tile size for tiling, but its
      // performance will improve significantly once sliding window is turned on.
      //
      // TODO: Register tiling is an important transformation especially for
      // benchmarks with significant reuse of the data (like matrix multiply and
      // convolutional layers). The mechanism for realizing register tiling is to
      // completely unroll small tiles of the innermost kernels. Unrolling
      // interacts with vectorization, storage layout, and depends on the outer
      // level tiling.
    struct Group {
          // The output stage representing the group.
      FStage output;
          // Functions that belong to the group.
      vector<FStage> members;
          // Members of the group which are inlined.
      set<string> inlined;
          // Tile sizes along dimensions of the output function of the group.
      map<string, Expr> tile_sizes;

      Group(const FStage &output, const vector<FStage> &members)
      : output(output), members(members) {}

      friend std::ostream& operator<<(std::ostream &stream, const Group &g) {
        stream << "Output FStage: " << g.output << '\n';
        stream << "Members: " << '{';
        for (size_t i = 0; i < g.members.size(); ++i) {
          if (i > 0) {
            stream << ", ";
          }
          stream << g.members[i];
        }
        stream << "}" << '\n';

        stream << "Inlined: " << '{';
        for (auto iter = g.inlined.begin(); iter != g.inlined.end(); ++iter) {
          if (std::distance(g.inlined.begin(), iter) > 0) {
            stream << ", ";
          }
          stream << *iter;
        }
        stream << "}" << '\n';

        stream << "Tile sizes: " << "{";
        for (auto iter = g.tile_sizes.begin(); iter != g.tile_sizes.end(); ++iter) {
          if (std::distance(g.tile_sizes.begin(), iter) > 0) {
            stream << ", ";
          }
          stream << "(" << iter->first << ", " <<  iter->second << ")";
        }
        stream << "}" << '\n';

        return stream;
      }
    };

      // Result of the analysis of a group.
    struct GroupAnalysis {
          // Estimate of the arithmetic and memory cost for computing the group.
      Cost cost;
          // Estimate of the parallelism that can be exploited while computing
          // the group.
      Expr parallelism;
          //map<string,Expr> footprints;
      Expr l2_footprint;
      Expr l3_footprint;

      GroupAnalysis() : cost(Cost()) , parallelism(Expr()) {}
      GroupAnalysis(const Cost &c, Expr p) : cost(c), parallelism(std::move(p)) {}

      inline bool defined() const {
        return cost.defined() && parallelism.defined();
      }

      void simplify() {
        cost.simplify();
        if (parallelism.defined()) {
          parallelism = Internal::simplify(parallelism);
        }
        if (l2_footprint.defined()){
          l2_footprint= Internal::simplify(l2_footprint);
        }
        if(l3_footprint.defined()){
          l3_footprint=Internal::simplify(l3_footprint);
        }
      }

      friend std::ostream& operator<<(std::ostream &stream, const GroupAnalysis &analysis) {
        stream << "[arith cost:" << analysis.cost.arith << ", ";
        stream << "memory cost:" << analysis.cost.memory << ", ";
        stream << "parallelism:" << analysis.parallelism << "]\n";
        return stream;
      }
    };

      // Configuration of a group and the corresponding analysis. A group is the
      // set of functions that are computed together in tiles and the group config
      // specifies at what granularity they are computed together ('tile_sizes').
    struct GroupConfig {
      map<string, Expr> tile_sizes;
      GroupAnalysis analysis;
      GroupConfig(const map<string, Expr> &tile_sizes, const GroupAnalysis &analysis)
      : tile_sizes(tile_sizes), analysis(analysis) {}
      GroupConfig() : tile_sizes(map<string, Expr>()), analysis(GroupAnalysis()) {}
    };

      // Cache for storing the best configuration for the grouping choice. During
      // the grouping process, the impact of grouping two groups together is only
      // limited to the producers and consumers of the groups that are being grouped
      // together. The best grouping choices for the rest of the pipeline need not be
      // re-evaluated and caching them improves performance significantly.
    map<GroupingChoice, GroupConfig> grouping_cache;

      // Each group in the pipeline has a single output stage. A group is comprised
      // of function stages that are computed together in tiles (stages of a function
      // are always grouped together). 'groups' is the mapping from the output stage
      // of the group to the group.
    map<FStage, Group> groups;
      // The child stages of each stage (i.e. stages that depend on or use the values
      // computed by a particular stage) in the pipeline.
    map<FStage, set<FStage>> children;
      // Map from the output stage of the group to the analysis of the group. The mapping
      // needs to be updated whenever the grouping changes.
    map<FStage, GroupAnalysis> group_costs;

      // Levels that are targeted by the grouping algorithm. In the 'Inline' mode, the grouping
      // algorithm groups the functions by inlining the expression for the producer function
      // into the consumer stage. In the 'FastMem' mode, the grouping is done at the level of
      // tiles of the group output stage.
    enum class Level {Inline, FastMem};

      // Bounds of each function stage in the pipeline. These bounds are inferred from the
      // estimates of the outputs and other functions in the pipeline.
    const map<string, Box> &pipeline_bounds;
      // Parameters of the machine model that is used for estimating the cost of each
      // group in the pipeline.
    const MachineParams &arch_params;
      // Dependency analysis of the pipeline. This support queries on regions
      // accessed and computed for producing some regions of some functions.
    DependenceAnalysis &dep_analysis;
      // The arithmetic and memory costs of evaluating the expressions which define
      // each function in the pipeline.
    RegionCosts &costs;
      // Output functions of the pipeline.
    const vector<Function> &outputs;

    Partitioner(const map<string, Box> &_pipeline_bounds,
      const MachineParams &_arch_params,
      const vector<Function> &_outputs,
      DependenceAnalysis &_dep_analysis,
      RegionCosts &_costs);

    void initialize_groups(); 
    vector<pipe_IR> optimize_pipe(vector<pipe_IR> pipes);
    //segment pipe
    void segment_pipeline(pipe_IR p,pipe_IR init_pipe,vector<pipe_IR> *segments,vector<pipe_IR> *best);
    void split_remainder(vector<pipe_IR> *current_segments,pipe_IR init_pipe, pipe_IR new_pipe, pipe_IR remainder_pipe,vector<pipe_IR> *best_segments);
    bool seg_costs(vector<pipe_IR> *new_segments, vector<pipe_IR> *old_segments);
    string find_new_output(pipe_IR p);
    bool is_complete_pipe(vector<pipe_IR> *segments,pipe_IR init_pipe);
    void find_parents(FStage st,pipe_IR p, set<string> *stage_parents);

    Group inline_trivials_in_group(const Group &prod_group,pipe_IR p);

    Group inline_rest(const Group &group,pipe_IR p);
      // Merge 'prod_group' into 'cons_group'. The output stage of 'cons_group'
      // will be the output stage of the merged group.
    Group merge_groups(const Group &prod_group, const Group &cons_group);

      // Merge 'prods' in 'choice' into 'cons'. Set the tile size of the new group
      // to the one specified by 'eval'. If 'level' is set to Inline, all members
      // of 'prods' will be inlined in the new group.
    void merge_groups(const GroupingChoice &choice, const GroupConfig &eval,
      Partitioner::Level level);

      // Given a grouping 'g', compute the estimated cost (arithmetic + memory) and
      // parallelism that can be potentially exploited when computing that group.
    GroupAnalysis analyze_group(const Group &g, bool show_analysis);

    GroupAnalysis analyze_group_new(const Group &g, pipe_IR p, bool show_analysis, bool to_inline);
    GroupAnalysis analyze_group_inline(const Group &g, pipe_IR p, bool show_analysis);
      // For each group in the partition, return the regions of the producers
      // need to be allocated to compute a tile of the group's output.
    map<string, Box> group_storage_bounds(const Group &g);

      // For each group in the partition, return the regions of the producers
      // required to compute a tile of the group's output.
    map<FStage, DimBounds> group_loop_bounds(const Group &g);

      // Partition the pipeline by iteratively merging groups until a fixpoint is
      // reached.
    void group(Partitioner::Level level);

      //analyize hte pipe
    pipe_IR analysis(pipe_IR pipe_init,bool will_inline, bool is_split, bool l2_constraint);

      //split the pipeline into segments
    vector<pipe_IR> split_pipe(pipe_IR p);

    void recursive_parenthood(FStage pst, pipe_IR r,set<string> *parents);

      // Given a grouping choice, return a configuration for the group that gives
      // the highest estimated benefits.
    GroupConfig evaluate_choice(const GroupingChoice &group, Partitioner::Level level);

      // Pick the best choice among all the grouping options currently available. Uses
      // the cost model to estimate the benefit of each choice. This returns a vector of
      // choice and configuration pairs which describe the best grouping choice.
    vector<pair<GroupingChoice, GroupConfig>>
    choose_candidate_grouping(const vector<pair<string, string>> &cands,
      Partitioner::Level level);

      // Return the bounds required to produce a function stage.
    DimBounds get_bounds(const FStage &stg);

      // Return the bounds required to produce a tile of a function stage.
    DimBounds get_bounds_from_tile_sizes(const FStage &stg,
     const map<string, Expr> &tile_sizes);

      // Return the estimated size of the bounds.
    map<string, Expr> bounds_to_estimates(const DimBounds &bounds);

      // Given a function stage, return a vector of possible tile configurations for
      // that function stage.
    vector<map<string, Expr>> generate_tile_configs(const FStage &stg, pipe_IR p);
    vector<map<string, Expr>> generate_tile_configs_old(const FStage &stg);
      // Find the best tiling configuration for a group 'g' among a set of tile
      // configurations. This returns a pair of configuration with the highest
      // estimated benefit and the estimated benefit.
    pair<map<string, Expr>, GroupAnalysis> find_best_tile_config(const Group &g);
    pair<map<string, Expr>, GroupAnalysis> find_best_tile_config_new(const Group &g, pipe_IR p, bool l2_constraint);

    vector<string> dims_to_tile(const FStage &stg, map<string,Expr> min_tiles);

      // Estimate the benefit (arithmetic + memory) of 'new_grouping' over 'old_grouping'.
      // Positive values indicates that 'new_grouping' may be preferrable over 'old_grouping'.
      // When 'ensure_parallelism' is set to true, this will return an undefined cost
      // if the estimated parallelism is smaller than the machine parameters.
      // If 'no_redundant_work' is set, we only consider the arithmetic cost, i.e. if
      // the arithmetic benefit is negative, we will treat it as no benefits and we
      // should not perform the new grouping.
    Expr estimate_benefit(const GroupAnalysis &old_grouping, const GroupAnalysis &new_grouping,
      bool no_redundant_work, bool ensure_parallelism);

      // Same as above; however, 'new_grouping' is a vector of function pairs that
      // are to be grouped together.
    Expr estimate_benefit(const vector<pair<GroupingChoice, GroupConfig>> &new_grouping,
      bool no_redundant_work, bool ensure_parallelism);

      // Return the total estimate on arithmetic and memory costs of computing all
      // groups within the pipeline.
    Cost get_pipeline_cost();

      // Return the maximum access stride to allocation of 'func_acc' along any
      // loop variable specified in 'vars'. Access expressions along each dimension
      // of the allocation are specified by 'acc_exprs'. The dimension bounds of the
      // allocation are specified by 'buffer_bounds'.
    Expr find_max_access_stride(const Scope<> &vars, const string &func_acc,
      const vector<Expr> &acc_exprs, const Box &buffer_bounds);

      // Return the sum of access strides along each of the loop variables in
      // a function stage. The bounds of all the allocations accessed are specified
      // in 'allocation_bounds'. Return an empty map if it can't figure out any of
      // the stride dimension.
    map<string, Expr> analyze_spatial_locality(
      const FStage &stg, const map<string, Box> &parent_bounds,
      const set<string> &inlines = set<string>());

    map<string,map<string, Expr>> evaluate_reuse(const FStage &stg, const set<string> &prods);
    vector<string> find_prods(const set<string>&prods);

    map<string,Expr> find_dims(const FStage &stg);

    map<string,Expr> remove_implicit_vars(const map<string,Expr> vars);
    vector<pipe_IR> find_luts(map<string, Function> env,std::map<string,map<string,map<string, Expr>>> reuse_per_stage,pipe_IR init_pipe);
    bool is_lut(const FStage &stg,std::map<string,map<string,map<string, Expr>>> reuse_per_stage);

    map<string,Expr> find_min_tile_dims(const FStage &stg, pipe_IR p);
      // Generate and apply schedules for all functions within a pipeline by
      // following their grouping structure.
      //
      // TODO: A mode where schedules are not applied to the functions might be
      // interesting.
      //
      // TODO: The current form of the schedule returned is not very useful since it
      // cannot be manipulated and introspected very easily. The problem is that all
      // of the scheduling uses internal function and variable names which are not
      // visible to the user. Additionally, functions like sum and maximum are not
      // user visible. More thought needs to go into interaction between the user and
      // auto scheduling.
    void generate_cpu_schedule(const Target &t, AutoSchedule &sched, pipe_IR p);

      // Same as \ref Partitioner::generate_cpu_schedule, but this generates and
      // applies schedules for a group of function stages.


    void generate_group_cpu_schedule(const Group &g, const Target &t,
     const map<FStage, DimBounds> &group_loop_bounds,
     const map<string, Box> &group_storage_bounds,
     const set<string> &inlines,
     AutoSchedule &sched, pipe_IR p, unsigned int out_st_num);

      // Split the dimension of stage 'f_handle' along 'v' into inner and outer
      // dimensions. Modify 'estimates' according to the split and append the split
      // schedule to 'sched'.
    pair<VarOrRVar, VarOrRVar> split_dim(
      const Group &g, Stage f_handle, int stage_num, Definition def,
      bool is_group_output, VarOrRVar v, const Expr &factor, string in_suffix,
      string out_suffix, map<string, Expr> &estimates, AutoSchedule &sched);

      // Loop over the dimensions of function stage 'f_handle' starting from innermost
      // and vectorize the first pure dimension encountered.
    void vectorize_stage(
      const Group &g, Stage f_handle, int stage_num, Definition def,
      Function func, bool is_group_output, const Target &t, set<string> &rvars,
      map<string, Expr> &estimates, AutoSchedule &sched, pipe_IR p);

      // Reorder the dimensions to preserve spatial locality. This function
      // checks the stride of each access. The dimensions of the loop are reordered
      // such that the dimension with the smallest access stride is innermost.
      // This takes the strides along each dimension as input.
    void reorder_dims(Stage f_handle, int stage_num, Definition def,
      map<string, Expr> strides, AutoSchedule &sched,map<string,Expr> sbounds);

      // Helper functions to display partition information of the pipeline.
    void disp_pipeline_costs();
    void disp_pipeline_bounds();
    void disp_pipeline_graph();
    void disp_grouping();
  };




  vector<pipe_IR> Partitioner::find_luts(map<string, Function> env,std::map<string,map<string,map<string, Expr>>> reuse_per_stage,pipe_IR init_pipe){
    vector<pipe_IR> new_pipe;
    int luts=0;
    new_pipe.push_back(init_pipe);
    for (const auto &f : env) {
      FindAllCalls find;
      f.second.accept(&find);
      int num_stages = f.second.updates().size() + 1;
      bool lut=true;
      for (int s = 0; s < num_stages; s++) {
        FStage curr_s(f.second, s);
           //   if(!curr_s.func.can_be_inlined()) continue;
        lut=is_lut(curr_s,reuse_per_stage);
    //    cout<<"curr_s ."<<curr_s.func.name()<<" lut "<<lut<<endl;
        if(!lut) break;

      }
      if(lut) {
        string lut_name=f.second.name();
        luts++;
      //  cout<<"erased "<<lut_name<<endl;
        new_pipe.push_back(pipe_IR());
        new_pipe[luts].pipe.emplace(lut_name,new_pipe[0].pipe[lut_name]);
        new_pipe[luts].pipe[lut_name].output=1;
        new_pipe[luts].output_func=lut_name;
        for (int s = 0; s < num_stages; s++) {
          FStage curr_s(f.second, s);
          new_pipe[luts].pipe_f.push_back(curr_s);

        }

        new_pipe[0].pipe.erase(lut_name);
        vector<FStage> fixed_group;
        for(const auto &st:new_pipe[0].pipe_f){
          if(st.func.name()!=lut_name)  fixed_group.push_back(st);
        }
        new_pipe[0].pipe_f=fixed_group;
      }
    }
    return new_pipe;
  }


  void Partitioner::disp_grouping() {
    debug(0) << "\n=========" << '\n';
    debug(0) << "Grouping:" << '\n';
    debug(0) << "=========" << '\n';
    for (const auto &g : groups) {
      debug(0) << g.second << '\n';
    }
    debug(0) << "=========" << '\n';
  }

  void Partitioner::disp_pipeline_graph() {
    debug(0) << "\n================" << '\n';
    debug(0) << "Pipeline graph:" << '\n';
    debug(0) << "================" << '\n';
    for (const auto &f : children) {
      debug(0) << f.first << ": {";
      for (auto iter = f.second.begin(); iter != f.second.end(); ++iter) {
        if (std::distance(f.second.begin(), iter) > 0) {
          debug(0) << ", ";
        }
        debug(0) << *iter;
      }
      debug(0) << "}" << '\n';
    }
    debug(0) << "================" << '\n';
  }

  void Partitioner::disp_pipeline_bounds() {
    debug(0) << "\n================" << '\n';
    debug(0) << "Pipeline bounds:" << '\n';
    debug(0) << "================" << '\n';
    disp_regions(pipeline_bounds);
    debug(0) << "===============" << '\n';
  }

  Cost Partitioner::get_pipeline_cost() {
    internal_assert(!group_costs.empty());

    Cost total_cost(0, 0);
    for (const pair<FStage, Group> &g : groups) {
      const GroupAnalysis &analysis = get_element(group_costs, g.first);
      if (!analysis.cost.defined()) {
        return Cost();
      }
      total_cost.arith += analysis.cost.arith;
      total_cost.memory += analysis.cost.memory;
    }
    total_cost.simplify();
    return total_cost;
  }

  void Partitioner::disp_pipeline_costs() {
    internal_assert(!group_costs.empty());
    Cost total_cost(0, 0);
    debug(0) << "\n===============" << '\n';
    debug(0) << "Pipeline costs:" << '\n';
    debug(0) << "===============" << '\n';
    debug(0) << "Group: (name) [arith cost, mem cost, parallelism]" << '\n';
    for (const pair<FStage, Group> &g : groups) {
      const GroupAnalysis &analysis = get_element(group_costs, g.first);
      if (!total_cost.arith.defined()) {
        continue;
      } else if (!analysis.cost.arith.defined()) {
        total_cost.arith = Expr();
      } else {
        total_cost.arith += analysis.cost.arith;
      }

      if (!total_cost.memory.defined()) {
        continue;
      } else if (!analysis.cost.memory.defined()) {
        total_cost.memory = Expr();
      } else {
        total_cost.memory += analysis.cost.memory;
      }

      debug(0) << "Group: " << g.first << " [";
      debug(0) << analysis.cost.arith << ", " << analysis.cost.memory
      << ", " << analysis.parallelism << "]\n";
    }
    total_cost.simplify();
    debug(0) << "Total arithmetic cost: " << total_cost.arith << '\n';
    debug(0) << "Total memory cost: " << total_cost.memory << '\n';
    debug(0) << "===============" << '\n';
  }

  // Construct a partitioner and build the pipeline graph on which the grouping
  // algorithm operates.
  Partitioner::Partitioner(const map<string, Box> &_pipeline_bounds,
   const MachineParams &_arch_params,
   const vector<Function> &_outputs,
   DependenceAnalysis &_dep_analysis,
   RegionCosts &_costs)
  : pipeline_bounds(_pipeline_bounds), arch_params(_arch_params),
  dep_analysis(_dep_analysis), costs(_costs), outputs(_outputs) {
      // Place each stage of a function in its own group. Each stage is
      // a node in the pipeline graph.
    for (const auto &f : dep_analysis.env) {
      if (!pipeline_bounds.count(f.first)) {
              // If a function does not have a pipeline bound (i.e. it can be
              // statically proven that no one ever uses it), we should not
              // consider it during the grouping.
        debug(5) << "Creating partitioner: ignore function \"" << f.first
        << "\" since it has empty pipeline bounds\n";
        continue;
      }
      int num_stages = f.second.updates().size() + 1;
      for (int s = 0; s < num_stages; s++) {
        FStage stg(f.second, s);
        Group g(stg, {stg});
        groups.insert(make_pair(stg, g));
      }
    }

      // Find the consumers of each function and use it to populate the children map.
    for (const auto &f : dep_analysis.env) {
      int num_stages = f.second.updates().size() + 1;
      for (int s = 0; s < num_stages; s++) {
        set<string> parents = get_parents(f.second, s);
        for (const string &c : parents) {
                  // Filter out the calls to pipeline inputs. 'env' only contains
                  // the functions computed and not the inputs.
          auto iter = dep_analysis.env.find(c);
          if ((c != f.first) && (iter != dep_analysis.env.end())) {
                      // Consumer depends only on the last stage of a producer
                      // with multiple stages.
            const Function &prod_func = iter->second;
            int final_stage = prod_func.updates().size();

            FStage prod_stage(prod_func, final_stage);
            FStage cons_stage(f.second, s);
            children[prod_stage].insert(cons_stage);
          }
        }

        if (s > 0) {
                  // Update the children map to reflect the dependencies between
                  // different stages of the same function.
          FStage prod_stage(f.second, s - 1);
          FStage cons_stage(f.second, s);
          children[prod_stage].insert(cons_stage);
        }
      }
    }
  }

  vector<pipe_IR> Partitioner::split_pipe(pipe_IR p){
    //find stages with >1 consumers
    pipe_IR remainder_pipe=p;
    pipe_IR actual_remainder;
    vector<pipe_IR> sp;
    set<string> new_roots;
    for(auto &st : p.pipe_f){
      if(st.func.name()==p.output_func) continue;
     // if(p.pipe[st.func.name()].is_inline)  continue;
      if(children.find(st)==children.end())  continue;
      set<FStage> prod_group_children = get_element(children, st);
      bool all_parents_inputs=true;
    //  bool recur_parents=false;
      for(const auto par:get_parents(st.func, st.stage_num)){
        if (dep_analysis.env.find(par) != dep_analysis.env.end()) all_parents_inputs=false;
      }
      if(p.pipe[st.func.name()].is_inline&&all_parents_inputs){
        cout<<"not splitting at "<<st.func.name()<<" because all parents are inputs"<<endl;
        continue;
      }

      if(prod_group_children.size()>1){
        cout<<"should split at "<<st.func.name()<<endl;
        new_roots.insert(st.func.name());
        set<string> parents = get_parents(st.func, st.stage_num);
        pipe_IR new_pipe;
        new_pipe.pipe[st.func.name()]=p.pipe[st.func.name()];
        new_pipe.pipe[st.func.name()].output=1;
        //cout<<"new output "<<st.func.name()<<endl;
        new_pipe.pipe[st.func.name()].is_inline=false;
        new_pipe.output_func=st.func.name();
        remainder_pipe.pipe.erase(st.func.name());
        for(const auto parent:parents){
          if(remainder_pipe.pipe.find(parent)==remainder_pipe.pipe.end()) continue;
          for(const auto st_it:p.pipe_f){
            if(st_it.func.name()==parent){
           //  cout<<"inserted "<<st_it.func.name()<<endl;
             new_pipe.pipe_f.push_back(st_it);
             new_pipe.pipe[parent]=p.pipe[parent];
             remainder_pipe.pipe.erase(parent);
         //    cout<<"erased "<<parent<<endl;
           }
         }
       }
       for(const auto st_it:p.pipe_f){
        if(st_it.func.name()==st.func.name()){
       //   cout<<"inserted "<<st_it.func.name()<<endl;
          new_pipe.pipe_f.push_back(st_it);
        }
      }
      cout<<"============================="<<endl;
      sp.push_back(new_pipe);
    }
  }

  //find singleton groups that were inlined

  //now we need to trace back to the parents of (the parents) to make sure that we didnt leave any weird dependencies in the remainder pipe
  for( auto &np:sp){
    vector<FStage> temp_pipe=np.pipe_f;
    set<string> deep_parents;

    for(const auto &st:np.pipe_f){
      recursive_parenthood(st,remainder_pipe,&deep_parents);
      //cout<<"finished recursion"<<endl;
      for(const auto parent:deep_parents){
      //  cout<<"par "<<parent<<endl;
        for(const auto st_it:p.pipe_f){
         // cout<<st_it.func.name()<<" parent "<<parent<<endl;
          if(st_it.func.name()==parent){
           if(p.pipe.find(parent)!=p.pipe.end())  {
            if(np.pipe.find(parent)!=np.pipe.end())  continue;
            //cout<<"inserted "<<st_it.func.name()<<" into group of "<<np.output_func<<endl;
            temp_pipe.push_back(st_it);

            np.pipe[parent]=p.pipe[parent];
            remainder_pipe.pipe.erase(parent);
         //  cout<<"erased "<<parent<<endl;
          }
        }
      }
    }
  }
  np.pipe_f=temp_pipe;
  }
  vector<pipe_IR> ap;
 // for(auto &nr:new_roots) cout<<nr<<endl;
    for(auto &np:sp){
   // if((p.pipe[np.output_func].is_inline)){
     bool all_members_root=true;
     bool all_parents_inlined=true;
     for(const auto mr:np.pipe){
     // cout<<"group of "<<np.output_func<<" member "<<mr.first<<endl;
      if(new_roots.find(mr.first)==new_roots.end()) all_members_root=false;
      if(!p.pipe[mr.first].is_inline) all_parents_inlined=false;
    }
    if(all_members_root)  cout<<"not inserting group of "<<np.output_func<<endl;
    else if(p.pipe[np.output_func].is_inline&&all_parents_inlined) cout<<"not inserting group of "<<np.output_func<<endl;
    else if(p.pipe[np.output_func].is_inline&&np.pipe.size()==1) cout<<"not inserting group of "<<np.output_func<<endl;
    else ap.push_back(np);
   //}
   //else ap.push_back(np);
  }


  //return ;
  cout<<"fixing remainder"<<endl;
  for(const auto rem_stages:remainder_pipe.pipe){
    actual_remainder.pipe[rem_stages.first]=rem_stages.second;
    for(const auto st_it:remainder_pipe.pipe_f){
      if(st_it.func.name()==rem_stages.first){
        //cout<<"inserted in the remainder "<<st_it.func.name()<<endl;
        actual_remainder.pipe_f.push_back(st_it);
      }
    }
  }
  ap.push_back(actual_remainder);

  for( auto &news:ap){
    news.min_tiles=p.min_tiles;
    /*cout<<"new group "<<news.output_func<<endl;
    cout<<"members "<<endl;
    for(const auto membs:news.pipe_f) {
      cout<<membs.func.name()<<endl;

    }
    cout<<"================"<<endl;*/
  }

  //while(true);
  return ap;
  }


  void Partitioner::recursive_parenthood(FStage st,pipe_IR r,set<string> *parents){
    for(const auto &par:get_parents(st.func,st.stage_num)){
      if(r.pipe.find(par)==r.pipe.end())  continue;
      if(st.func.name()==par) continue;
      parents->insert(par);
    //  cout<<"new parent "<<par<<" in "<<st.func.name()<<endl;
      for(const auto &pst:r.pipe_f){
        if(pst.func.name()==par){
          recursive_parenthood(pst,r,parents);
        }
      }
    //}
    }
    return;

  }



  pipe_IR Partitioner::analysis(pipe_IR p,bool will_inline, bool is_split,bool l2_constraint){

    //cout<<"analysis"<<endl;
    // p.print_pipe();
    // stg.func, stg.stage_num
    //  Function f=p.pipe_f[p.output_func].func;
    //  FStage output_stage(prod_f, s);
    //find the output stage
    //fix the bounds if it's split!

    Function f;
   // cout<<"out  before bounds"<<p.output_func<<endl;
    
    int n_st=0;
    for(const auto &qq:p.pipe_f){
     // cout<<"qq.func.name()"<<qq.func.name()<<endl;
      if(is_split){
        map<string,Expr> new_bounds=find_dims(qq);
        if(qq.stage_num==p.pipe[qq.func.name()].stage_num) p.pipe[qq.func.name()].vars=new_bounds;
        if((p.pipe[qq.func.name()].output)||qq.func.name()==p.output_func){
          if(qq.stage_num==p.pipe[qq.func.name()].stage_num)  p.bounds=new_bounds;
        } 
      }
      if((p.pipe[qq.func.name()].output)||qq.func.name()==p.output_func){
       if(qq.stage_num==p.pipe[qq.func.name()].stage_num){
        f=qq.func;

        n_st=qq.stage_num;
            //  break;
      }
      }
    }
      //std::vector<FStage> members;
      //Function f=p.pipe_f[p.pipe_f.size()-1].func;
      //int n_st=p.pipe_f[p.pipe_f.size()-1].stage_num;
    FStage output_stage(f,n_st);
    //cout<<"output "<<output_stage.func.name()<<endl;
    Group g_init(output_stage,p.pipe_f);
    //cout<<"before min tiles"<<endl;
    map<string,Expr> min_tiles;
    if(!is_split){

      min_tiles=find_min_tile_dims(output_stage,p);

    }
    else{
     min_tiles=p.min_tiles;
     map<string,Expr> min_tilesn;
     min_tilesn=find_min_tile_dims(output_stage,p);
     for(const auto &mints:min_tilesn){
       // cout<<"bound in "<<mints.first<<" "<<p.bounds[mints.first]<<" min tile "<<mints.second<<endl;
        //if(min_tiles.find(mints.first)==min_tiles.end())  min_tiles.emplace(mints.first,mints.second/arch_params.parallelism);
      if(min_tiles[mints.first].defined()&&p.bounds[mints.first].defined()&&can_prove(p.bounds[mints.first]<=min_tiles[mints.first])){
        if(can_prove(mints.second>0)){
      //    cout<<"new bounds in "<<mints.first<<" "<<mints.second<<endl;
          min_tiles[mints.first]=mints.second;
        }
        else{
          //    cout<<"new bounds in "<<mints.first<<" "<<mints.second<<endl;
          min_tiles[mints.first]=p.bounds[mints.first]/arch_params.parallelism;
        }
      }

    }
  }
  //cout<<"after min tiles "<<endl;

  for( auto &mt:min_tiles){
    if(!mt.second.defined())  mt.second=make_zero(Int(32));
    //cout<<mt.first<<" "<<mt.second<<endl;
  }
      //cout<<"mins done"<<endl;
  p.min_tiles=min_tiles;
  p.create_nest();
     // p.print_pipe();
      //cout<<"nest done"<<endl;
  pipe_IR q=p;
  pipe_IR best=q;
  best.total_cost=make_const(Float(64),DBL_MAX);
  best.wset=make_const(Int(64),INT_MAX);
   // cout<<"best wset "<<best.wset<<endl;
  best.wset_l2=make_const(Int(64),INT_MAX);
      //string so="";
  vector <string> so;
  vector <string> io;
      //string io="";
  io.push_back(p.pipe[p.output_func].cols[0]);
  for(std::map<string,Expr>::iterator iti=p.inter_order.begin();iti!=p.inter_order.end();++iti){
    if(iti->first!=p.pipe[p.output_func].cols[0])   so.push_back(iti->first);
         //  so+=iti->first;
  }
      ////cout<<so<<endl;
  do{
    vector<string> ol;
    ol.insert( ol.end(), io.begin(), io.end() );
    ol.insert( ol.end(), so.begin(), so.end() );
      //string ol=io+so;
    vector<string> si;
      //string si="";
    for(std::map<string,Expr>::iterator iti=p.intra_order.begin();iti!=p.intra_order.end();++iti){
      if(can_prove(p.bounds[iti->first]>32)&&(iti->first!=p.pipe[p.output_func].cols[0]))     si.push_back(iti->first);

    }
    vector<string> sk;
     // string sk="";
     // #ifdef debug
      //cout<<"col "<<p.pipe[p.output_func].cols[0]<<endl;
      //cout<<endl;
   //   #endif
    for(std::map<string,Expr>::iterator iti=p.intra_order.begin();iti!=p.intra_order.end();++iti){

      if(can_prove(p.bounds[iti->first]<=32))    sk.push_back(iti->first);


    }

    sk.push_back(p.pipe[p.output_func].cols[0]);
    /*for(std::map<string,Expr>::iterator iti=p.intra_order.begin();iti!=p.intra_order.end();++iti){

      if(can_prove(p.bounds[iti->first]<=64)&&can_prove(p.bounds[iti->first]>16))    sk.push_back(iti->first);


    }*/
      //sk+=p.pipe[p.output_func].cols[0];



    q.interchange(0,ol);

    pair<map<string, Expr>, GroupAnalysis> best_analysis;
    sort(begin(si),end(si));
      ////cout<<"init "<<si<<endl;
     // //cout<<so<<endl;
    do{
    //  cout<<"interchange"<<endl;
      vector<string> il;
      il.clear();
      il.insert( il.end(), sk.begin(), sk.end() );
      il.insert( il.end(), si.begin(), si.end() );
         // il=sk+si;
         // //cout<<il<<endl;
      q.interchange(1,il);
     //   q.print_pipe();
      q.default_granularity();

    //  cout<<"before opt"<<endl;
      //q.print_pipe();
      q.optimize_granularity();
    //  cout<<"after opt"<<endl;
      //q.print_pipe();
      for(const auto &st:q.pipe){
        if(st.second.is_inline){
      //    cout<<"new group inlined "<<st.first<<endl;
                               // q.pipe.erase(q.pipe.find(st.first));
          g_init.inlined.insert(st.first);
        }    
      }
          //Group g_i=inline_trivials_in_group(g_init,q);

      Group g=g_init;
      if(will_inline){
     //   cout<<"before inl rest"<<endl;
        g=inline_rest(g_init,q);
     //   cout<<"inline rest done "<<endl;
        for(const auto &inl:g.inlined){
          if(!q.pipe[inl].is_inline){
      //      cout<<"new group inlined "<<inl<<endl;
                  //q.pipe.erase(q.pipe.find(inl));
            q.pipe[inl].is_inline=true;    
          }

        }
      }
        //  cout<<"finished first inlining"<<endl;
        /*  Group g=inline_rest(g0,q);
          for(const auto &inl:g.inlined){
              if(!q.pipe[inl].is_inline){
                  cout<<"new group inlined "<<inl<<endl;
                  q.pipe[inl].is_inline=true;    
              }
              
          }
          cout<<"finished second inlining"<<endl;*/
      //   cout<<"after opt"<<endl;
      //    q.print_pipe();

          // Tile sizes along dimensio
          //double t1=current_time_ir();
      if(l2_constraint) best_analysis=find_best_tile_config_new(g,q,true);
      else best_analysis=find_best_tile_config_new(g,q,false);
          //double t2=current_time_ir();
          //cout<<"time looking for tile size "<<(t2-t1)<<endl;
   //   cout<<"ftcn done"<<endl;
      q.tiles=best_analysis.first;
          /*for(const auto &tilit:best_analysis.first){
              cout<<"tilit "<<tilit.first<<" "<<tilit.second;
         }*/
      q.total_cost=best_analysis.second.cost.memory;
       //   q.print_pipe();
       //   Group g;
      //  //cout<<to_string(l.total_cost)<<endl;
      if((q.total_cost.defined())&&(best_analysis.second.l3_footprint.defined())&&can_prove(q.total_cost<=best.total_cost)){
          //cout<<"new best\n\n\n\n\n\n\n\n\n\n"<<endl;
            //  q.print_pipe();

        best=q;
        best.wset=best_analysis.second.l3_footprint;
        best.wset_l2=best_analysis.second.l2_footprint;
      }
      //  best.print_pipe();
      //  printf("%f\n %f\n",l.total_cost,best.total_cost);
    }while(std::next_permutation(si.begin(),si.end()));
  }while(std::next_permutation(so.begin(),so.end()));
   // cout<<"FOUND BEST "<<best.wset<<endl;
      //if te best was the initial non-analyzed one then put the inlines into that one as well (so we dont have to repeat it later)
  if(can_prove(best.wset==INT_MAX)){
    for(const auto &st:q.pipe){
      if(st.second.is_inline){
      //  cout<<"new remainder inlined "<<st.first<<endl;
                               // q.pipe.erase(q.pipe.find(st.first));
        best.pipe[st.first].is_inline=true;
      }    
    }
  }
  /*if(can_prove(best.wset==INT_MAX)){
    //best.print_pipe();
    cout<<"ERROR HERE DIDNT FIND BEST"<<endl;
    //while(true);
  }*/
  //else best.print_pipe();

  return best;




  }






  vector<pipe_IR> Partitioner::optimize_pipe(vector<pipe_IR> pipes){

   vector<pipe_IR> optimized_pipes;
   for(int i=0;i<(int)pipes.size();i++){
    pipe_IR q;
    if(pipes[i].pipe.size()>1){
      q=analysis(pipes[i],true,false,true);


      if(can_prove(q.wset>2*arch_params.last_level_cache_size)){
        vector<pipe_IR> new_pipes;
        
        cout<<"SHOULD SPLIT THIS "<<endl<<endl<<endl;
        //split the pipeline into all that have multiple children
        new_pipes=split_pipe(q);
     //   cout<<"returned split "<<new_pipes.size()<<endl;
        //if none had multiple children just go ahead to segmentation
        if(new_pipes.size()>1){
          for(int ii=0;ii<(int)new_pipes.size();ii++){
            pipe_IR nps=new_pipes[ii];
            pipe_IR l;
            if(nps.pipe.size()>1){
              l=analysis(nps,false,true,true);
             
              vector<pipe_IR> new_pipes;
              
       //       cout<<"q.wset "<<simplify(l.wset)<<" l2 "<<simplify(l.wset_l2)<<endl;
              if(can_prove(l.wset>2*arch_params.last_level_cache_size)){
                //split it into smaller ones
                vector<pipe_IR> segments;
                vector<pipe_IR> best;
                
                segment_pipeline(l,l,&segments,&best);
                
                
                for(const auto &segs:best)  optimized_pipes.push_back(segs);
              }
            else optimized_pipes.push_back(l);
          }
          else optimized_pipes.push_back(nps);
        }
      }
      else{
        pipe_IR ll=analysis(q,false,false,false);
        
        ll.print_pipe();
        //while(true);
        //else split into segments (no stages had multiple children)
        vector<pipe_IR> segments;
        vector<pipe_IR> best;
        segment_pipeline(ll,ll,&segments,&best);
        for(const auto &segs:best)  optimized_pipes.push_back(segs);

      }
  }
      //the initial solution fits (usually here)
  else optimized_pipes.push_back(q);
  }
    //just for the luts it stays just a single stage
  else   optimized_pipes.push_back(pipes[i]); 

  }
  return optimized_pipes;
  }








  void Partitioner::find_parents(FStage st,pipe_IR p,set<string> *stage_parents){
    
    bool is_not_input=(dep_analysis.env.find(st.func.name()) != dep_analysis.env.end());
    if(!is_not_input)  return;
    set<string> parents = get_parents(st.func, st.stage_num);
    for(const auto &par:parents){
      if(stage_parents->find(par)!=stage_parents->end()){
        continue;
      }
     
      bool par_in_pipe=p.pipe.find(par)!=p.pipe.end();
      bool par_is_not_input=(dep_analysis.env.find(par) != dep_analysis.env.end());
      


      if(par_in_pipe&&par_is_not_input){
    


    
       stage_parents->insert(par);


       

       for(const auto &stgs:p.pipe_f){
        if(stgs.func.name()==par){
          Function f=stgs.func;
          int n_st=stgs.stage_num;
          FStage new_par(f,n_st);
          find_parents(new_par,p,stage_parents);
        }
      }
    }

  }
  return;
  }


  string Partitioner::find_new_output(pipe_IR p){

    for(const auto &st:p.pipe_f){
      if(children.find(st)==children.end()) return st.func.name();
      set<FStage> possible_children = get_element(children, st);
      for(const auto &c:possible_children){
        if(p.pipe.find(c.func.name())==p.pipe.end())  return st.func.name();
      }
    }
    return "";
  }

  bool Partitioner::is_complete_pipe(vector<pipe_IR> *segments,pipe_IR init_pipe){  
    for(const auto stages:init_pipe.pipe){
      bool is_scheduled=false;
      for(const auto &seg:*segments){
        if(seg.pipe.find(stages.first)!=seg.pipe.end()) is_scheduled=true;
      }
      if(!is_scheduled) return 0;
     
    }
    return 1; 
  }

  bool Partitioner::seg_costs(vector<pipe_IR> *new_segments, vector<pipe_IR> *old_segments){
    Expr new_cost=make_zero(Int(64));
    for(const auto &p:*new_segments){
     if(p.total_cost.defined())   new_cost+=p.total_cost;;

   }
   new_cost=simplify(new_cost);
   Expr old_cost=make_zero(Int(64));
   for(const auto &p:*old_segments){
    if(p.total_cost.defined())    old_cost+=p.total_cost;

  }
  old_cost=simplify(old_cost);
  //cout<<"new_cost "<<new_cost<<endl;
  //cout<<"old cost "<<old_cost<<endl;
  if(can_prove(new_cost<old_cost))  return 1;
  return 0;
  }

  void Partitioner::split_remainder(vector<pipe_IR> *current_segments,pipe_IR init_pipe, pipe_IR new_pipe, pipe_IR remainder_pipe,vector<pipe_IR> *best_segments){
  //fix the remainder pipe
    if(remainder_pipe.pipe.size()>1){
      pipe_IR opt_rem=analysis(remainder_pipe,false,true,false);
      if(can_prove(opt_rem.wset<arch_params.last_level_cache_size)){
        current_segments->push_back(opt_rem);
        if(is_complete_pipe(current_segments,init_pipe)){
          if(best_segments->size()==0) *best_segments=*current_segments;
          else{
            if(seg_costs(current_segments,best_segments)) *best_segments=*current_segments;
          }

        }
        return;
      }
      else{
      //start splitting again
        for(const auto &st:remainder_pipe.pipe_f){
          pipe_IR new_pipe;

          //only split at the relevant update definition (since we add all updates anyway)
         
          if(remainder_pipe.pipe[st.func.name()].is_inline)  continue;
         // if(!remainder_pipe.pipe[st.func.name()].store_inter) continue;
            //find all parents
          int final_stage = st.func.updates().size();
       //   cout<<"stage "<<st.func.name()<<" has "<<final_stage<<" updates"<<endl;
          if((final_stage>0)&&st.stage_num!=remainder_pipe.pipe[st.func.name()].stage_num)  continue;
          new_pipe.pipe.emplace(st.func.name(),init_pipe.pipe[st.func.name()]);
          new_pipe.output_func=st.func.name();
         // new_pipe.pipe_f.push_back(st);
              for(const auto &sts:remainder_pipe.pipe_f){
      if(sts.func.name()==st.func.name()) new_pipe.pipe_f.push_back(st);
    }
          new_pipe.pipe[st.func.name()].output=1;
          new_pipe.min_tiles=remainder_pipe.min_tiles;
          set<string> stage_parents;
          for(const auto &nst:remainder_pipe.pipe_f){

          if(nst.func.name()==st.func.name()) find_parents(nst,remainder_pipe,&stage_parents);
        }
          int npsize=0;
          for(const auto &pars:stage_parents){
         //   cout<<"consumes "<<pars<<endl;
            new_pipe.pipe.emplace(pars,remainder_pipe.pipe[pars]);
            if(!new_pipe.pipe[pars].is_inline)  npsize++;
            new_pipe.pipe[pars].output=0;
            for(const auto &stgs:remainder_pipe.pipe_f){
              if(stgs.func.name()==pars) new_pipe.pipe_f.push_back(stgs);  
            }




          }
          if(npsize<=4)  continue;
          if(new_pipe.pipe.size()==remainder_pipe.pipe.size()) continue;
          pipe_IR sched_new;
          if(new_pipe.pipe.size()==1) sched_new=new_pipe;
          else {
            sched_new=analysis(new_pipe,false,true,false);
            if(can_prove(sched_new.wset>arch_params.last_level_cache_size))  continue;
          }
          cout<<"new recur root "<<sched_new.output_func<<endl;
          current_segments->push_back(sched_new);
          if(sched_new.pipe.size()==0)  cout<<"ERROR NEW"<<endl;

         // cout<<"=============================="<<endl;
            //create the new remainder and split again
              //now create the remainder pipe
          pipe_IR next_remainder;
          for(const auto &st:remainder_pipe.pipe){
            if(new_pipe.pipe.find(st.first)==new_pipe.pipe.end()){
              next_remainder.pipe.emplace(st.first,st.second);
              next_remainder.pipe[st.first].output=0;
              for(const auto &stgs:remainder_pipe.pipe_f){
                if(stgs.func.name()==st.first)  next_remainder.pipe_f.push_back(stgs);
              }
            }
          }

          //find the new output func;
          if(next_remainder.pipe.size()==remainder_pipe.pipe.size()) continue;
          string new_out=find_new_output(next_remainder);
          next_remainder.output_func=new_out;
          next_remainder.pipe[new_out].output=1;
          next_remainder.min_tiles=remainder_pipe.min_tiles;
      //    cout<<"new output of remainder pipe "<<new_out<<endl;
      //    cout<<"members"<<endl;
       //   for(const auto &pp:next_remainder.pipe) cout<<pp.first<<endl;
          pipe_IR sched_rem;
            //if(next_remainder.pipe.size()>0){


          if(sched_rem.pipe.size()!=0)  current_segments->push_back(sched_rem);

          split_remainder(current_segments,init_pipe ,next_remainder,next_remainder,best_segments);
          current_segments->erase(current_segments->end()-1);
            //}
      //    cout<<"pushing remainder"<<endl;


        //cout<<k<<endl;

       //   cout<<"=============================="<<endl;



        }
      }
    }else if(remainder_pipe.pipe.size()==1){
      current_segments->push_back(remainder_pipe);
      if(is_complete_pipe(current_segments,init_pipe)){
        if(best_segments->size()==0) *best_segments=*current_segments;
        else{
          if(seg_costs(current_segments,best_segments)) *best_segments=*current_segments;
        }

      }
      return;

    }else{
      if(is_complete_pipe(current_segments,init_pipe)){
        if(best_segments->size()==0) *best_segments=*current_segments;
        else{
          if(seg_costs(current_segments,best_segments)) *best_segments=*current_segments;
        }

      }
      return;
    }

  }


  void Partitioner::segment_pipeline(pipe_IR p, pipe_IR init_pipe,vector<pipe_IR> *segments,vector<pipe_IR> *best){
      //initialize the split


   for(const auto &st:p.pipe_f){
    pipe_IR new_pipe;

    if(p.pipe[st.func.name()].is_inline)  continue;
  //  if(!p.pipe[st.func.name()].store_inter) continue;
      //find all parents
    int final_stage = st.func.updates().size();
    //cout<<"stage "<<st.func.name()<<" has "<<final_stage<<" updates and og was "<<init_pipe.pipe[st.func.name()].stage_num<<endl;
    //if((int)st.stage_num<final_stage)  continue;
    if((final_stage>0)&&st.stage_num!=init_pipe.pipe[st.func.name()].stage_num)  continue;
    new_pipe.pipe.emplace(st.func.name(),init_pipe.pipe[st.func.name()]);
    new_pipe.output_func=st.func.name();
   // new_pipe.pipe_f.push_back(st);
    new_pipe.pipe[st.func.name()].output=1;
    for(const auto &sts:p.pipe_f){
      if(sts.func.name()==st.func.name()) new_pipe.pipe_f.push_back(st);
    }
    new_pipe.min_tiles=p.min_tiles;
    
    set<string> stage_parents;
    for(const auto &nst:p.pipe_f){
    if(nst.func.name()==st.func.name()) find_parents(nst,p,&stage_parents);
  }
    //find_parents(st,p,&stage_parents);
    int npsize=0;
    for(const auto &pars:stage_parents){
     // cout<<"consumes "<<pars<<endl;
      new_pipe.pipe.emplace(pars,p.pipe[pars]);
      new_pipe.pipe[pars].output=0;
      if(!new_pipe.pipe[pars].is_inline)  npsize++;
      for(const auto &stgs:p.pipe_f){
        if(stgs.func.name()==pars) new_pipe.pipe_f.push_back(stgs);  
      }




    }
    new_pipe.print_pipe();
    if(new_pipe.pipe.size()==init_pipe.pipe.size()) continue;
    if(npsize<=4)  continue;
    pipe_IR sched_new;
    if(new_pipe.pipe.size()==1) sched_new=new_pipe;
    else {
      sched_new=analysis(new_pipe,false,true,false);
      if(can_prove(sched_new.wset>arch_params.last_level_cache_size))  continue;
    }
    cout<<"new root "<<sched_new.output_func<<endl;
    //  sched_new.print_pipe();
    if(sched_new.pipe.size()==0)  cout<<"ERROR NEW b4 rem"<<endl; 
    segments->push_back(sched_new);


   // cout<<"=============================="<<endl;
      //now create the remainder pipe
    pipe_IR remainder_pipe;
    for(const auto &st:p.pipe){
      if(new_pipe.pipe.find(st.first)==new_pipe.pipe.end()){
        remainder_pipe.pipe.emplace(st.first,st.second);
        remainder_pipe.pipe[st.first].output=0;
        for(const auto &stgs:p.pipe_f){
          if(stgs.func.name()==st.first)  remainder_pipe.pipe_f.push_back(stgs);
        }
      }
    }
      //find the new output func;

    if(remainder_pipe.pipe.size()==p.pipe.size()) continue;
    string new_out=find_new_output(remainder_pipe);
    remainder_pipe.output_func=new_out;
    remainder_pipe.pipe[new_out].output=1;
    remainder_pipe.min_tiles=p.min_tiles;
   // cout<<"new output of remainder pipe "<<new_out<<endl;
   // cout<<"members"<<endl;
   // for(const auto &pp:remainder_pipe.pipe) cout<<pp.first<<endl;
    pipe_IR sched_rem;
    if(remainder_pipe.pipe.size()>0){

      if(sched_rem.pipe.size()!=0)  segments->push_back(sched_rem);
      split_remainder(segments,init_pipe ,remainder_pipe,remainder_pipe,best);
      segments->clear();
    }
   // cout<<"pushing remainder"<<endl;


        //cout<<k<<endl;

   // cout<<"=============================="<<endl;

  }




  }




  void Partitioner::initialize_groups() {
    for (pair<const FStage, Group> &g : groups) {
      pair<map<string, Expr>, GroupAnalysis> best = find_best_tile_config(g.second);
      g.second.tile_sizes = best.first;
      group_costs.emplace(g.second.output, best.second);
    }
    grouping_cache.clear();
  }


  Partitioner::Group Partitioner::inline_trivials_in_group(const Group &init_g,pipe_IR p) {

    map<string, Expr> footprints;
    set<string> group_members;
    Group inlined_group=init_g;
    for (const auto &st : p.pipe_f) {
      group_members.insert(st.func.name());
      if(p.pipe[st.func.name()].is_inline)    inlined_group.inlined.insert(st.func.name());
     //     cout<<"member "<<st.func.name()<<endl;
    }

    for(const auto &it:init_g.members){

      map<string,Expr> cost_ov;
      string func_name=it.func.name();
      Expr inline_cost=make_zero(Int(64));
      Expr inline_cost_prod=make_zero(Int(64));
      if(it.func.name()==init_g.output.func.name())   continue;   
      if(p.pipe[func_name].is_inline) continue;
      if(!it.func.can_be_inlined())   continue;
      if(!is_func_trivial_to_inline_memb(it.func))    continue;
  //    cout<<"prod "<<func_name<<endl;

   //   cout<<"inl prod cost"<<endl;
      for(const auto &reit:p.pipe[func_name].re){
        string prod=reit.first;

      //bool is_function = (dep_analysis.env.find(prod) != dep_analysis.env.end());
        bool is_member = group_members.find(prod)!=group_members.end();
        if(find(p.pipe[func_name].producers.begin(),p.pipe[func_name].producers.end(),reit.first)==p.pipe[func_name].producers.end())   continue;
   //   if(group_members.find(reit.first)==group_members.end()) continue;
        if(reit.first==it.func.name())  continue;   
        if(is_member &&(!p.pipe[prod].is_inline))   continue;

        for(const auto &ov:reit.second){
          if(!ov.second.defined())    continue;
          string var_ov=get_expr_str(ov.first);
          if(p.pipe[init_g.output.func.name()].vars.find(var_ov)==p.pipe[init_g.output.func.name()].vars.end()){
          //    cout<<"skipping overlap in "<<reit.first<<" var "<<ov.first<<endl;
            continue;
          }   
    //      cout<<reit.first<<" ov "<<ov.first<<" amount "<<ov.second<<endl;
          string dim_str=(ov.first);
          if(!cost_ov[dim_str].defined())  cost_ov[dim_str]=ov.second;
          else cost_ov[dim_str]=can_prove(ov.second>cost_ov[dim_str])?ov.second:cost_ov[dim_str];
        }
      }

      Expr partial_cost=make_one(Int(64));
      for(const auto &ovs:cost_ov){
        if(can_prove(ovs.second!=0)) partial_cost=partial_cost*ovs.second;
      }
      partial_cost=simplify(partial_cost);
      inline_cost_prod=partial_cost;
      cost_ov.clear();
   //   cout<<"inl call cost"<<endl;
      //toodo add more only if it wasnt captured
      //for(const FStage &c : p.pipe_f) {
     // if(get_element(children,it).size()==1)   continue;
      for (const FStage &c : get_element(children, it)) {
        string consumer=c.func.name();
        string consumer_compute;
        if(!p.pipe[consumer].is_root)   consumer_compute=get_expr_str(p.pipe[consumer].compute.second);
        map<string,Expr> cons_ov;
        for(const auto ov:p.pipe[consumer].re[it.func.name()]){
          if(!ov.second.defined())    continue;
          //find if the overlap exists in the output stage or if it's captured anyway
          bool is_captured=false;
          if(p.intra_order.find(ov.first)==p.intra_order.end()) is_captured=true;
          else if(p.pipe[consumer].is_root)   is_captured=true;
          else if(p.pipe[consumer].compute_inter)   is_captured=true;
          else if(p.pipe[consumer].is_inline)   is_captured=false;
          else if(can_prove(p.intra_order[consumer_compute]>p.intra_order[ov.first]))   is_captured=true;
          if(is_captured) continue;
  //        cout<<c.func.name()<<" ov "<<ov.first<<" amount "<<ov.second<<endl;
          string dim_str=(ov.first);
          if(!cost_ov[dim_str].defined())  cost_ov[dim_str]=ov.second;
          else cost_ov[dim_str]=can_prove(ov.second>cost_ov[dim_str])?ov.second:cost_ov[dim_str];
          cons_ov[dim_str]=ov.second;
        }
        if(find(p.pipe[c.func.name()].producers.begin(),p.pipe[c.func.name()].producers.end(),func_name)==p.pipe[c.func.name()].producers.end())   continue;
        Expr partial_cost=make_one(Int(64));
        for(const auto &ovs:cons_ov){
          if(can_prove(ovs.second!=0)) partial_cost=partial_cost*ovs.second;
        }
        partial_cost=simplify(partial_cost*inline_cost_prod);
        inline_cost+=partial_cost;

      }
      Expr cost=make_one(Int(64));
      for(const auto &ovs:cost_ov){
       if(can_prove(ovs.second!=0)) cost=cost*ovs.second;
     }
     cost=simplify(cost);

     inline_cost=simplify((inline_cost));




     if((can_prove(inline_cost<=cost)||can_prove(inline_cost<=1)))  inlined_group.inlined.insert(it.func.name());
     cout<<" inl cost "<<inline_cost<<" cost "<<cost<<endl<<endl<<endl<<endl<<endl;

   }

   return inlined_group;
  }

  Partitioner::Group Partitioner::inline_rest(const Group &init_g,pipe_IR p) {



    GroupAnalysis group_analysis_init;
    GroupAnalysis group_analysis_inline;
    Group inline_test_group=init_g;
    Group inlined_group=init_g;

  // Set the tile sizes to one along all dimensions of the consumer group
    map<string, Expr> tile_sizes;

  //const Function &cons_f = init_g.output.func;
   // cout<<"before dims to tile"<<endl;
    vector<string> tile_vars=dims_to_tile(init_g.output,p.min_tiles);
    //cout<<"after dims to tile"<<endl;
  //const vector<Dim> &dims = get_stage_dims(cons_f, init_g.output.stage_num);
    for (const auto &q_vars:tile_vars) {
      tile_sizes.emplace(q_vars,16);
    }
    inlined_group.tile_sizes=tile_sizes;
    inline_test_group.tile_sizes=tile_sizes;
  //  cout<<"before analyze new "<<endl;
    group_analysis_init=analyze_group_new(inlined_group,p,false,true);
  //  cout<<"after analyze new "<<endl;
    for (const FStage &it : inline_test_group.members) {
      if(it.func.name()==init_g.output.func.name())   continue;   
      if(!it.func.can_be_inlined())   continue;
      if(inline_test_group.inlined.find(it.func.name())!=inline_test_group.inlined.end()) continue;
      //split the group
      inline_test_group=inlined_group;


      //group_analysis_init=analyze_group(inlined_group,false);
      inline_test_group.inlined.insert(it.func.name());
     // cout<<"analyzing inline for "<<it.func.name()<<endl;
      //group_analysis_inline=analyze_group_new(inline_test_group,p,false);
     // cout<<"before analyze new test"<<endl;
      group_analysis_inline=analyze_group_new(inline_test_group,p,false,true);
     // cout<<"after analyze new test"<<endl;
      Expr benefit=estimate_benefit(group_analysis_init,group_analysis_inline,false,false);
      if(benefit.defined()&&can_prove(benefit>0)){
        group_analysis_init=group_analysis_inline;
        //  cout<<"it.func "<<it.func.name()<<" will be inlined "<<endl;
        inlined_group.inlined.insert(it.func.name());
      }
    }
    return inlined_group;
  }

  map<string,Expr> Partitioner::find_dims(const FStage &stg){


    Expr order=make_zero(Int(64));
    map<string,Expr> dim_order;
    //cout<<stg.func.name()<<" finding dims"<<endl;
      // Partitioner::get_bounds(const FStage &s)
    const map<string, Interval> &def_bounds = get_bounds(stg);
    const vector<Dim> &dims = get_stage_dims(stg.func,stg.stage_num);
    for(int d=0;d<(int)dims.size()-1;d++){
   //  cout<<dims[d].var;
     const Interval &bound = get_element(def_bounds, dims[d].var);
     Expr extent = get_extent(bound);
     dim_order[dims[d].var]=extent;
         // order=simplify(order+1);
   }
   return dim_order;
  }



  bool Partitioner::is_lut(const FStage &stg,std::map<string,map<string,map<string, Expr>>> reuse_per_stage){
    set<string> parents = get_parents(stg.func, stg.stage_num);
   // cout<<"stg.func.name() "<<stg.func.name()<<" par size "<<parents.size()<<endl;
   // for(const auto &pp:parents) cout<<pp<<endl;
    if(parents.size()>0){
      if(parents.size()==1&&parents.find(stg.func.name())==parents.end()) return 0;
      else if(parents.size()>1) return 0;
    }
    const map<string, Interval> &def_bounds = get_bounds(stg);
  //  cout<<"is lut for "<<stg.func.name()<<endl;
    const vector<Dim> &dims = get_stage_dims(stg.func, stg.stage_num);
    if(dims.size()==2)  return 1;
    map<string,bool> full_reuse;
    for(int i=0;i<(int)dims.size();i++){
      if(dims[i].is_rvar()) continue;
      full_reuse.emplace(dims[i].var,0);
    }
    for(const auto &st:reuse_per_stage){
      if(st.first==stg.func.name()) continue;

      const auto &re=st.second.find(stg.func.name());
      if (re!=st.second.end()){ 

        for(const auto &var:re->second){
          if(full_reuse.find(var.first)==full_reuse.end())  continue;
          const Interval &bound = get_element(def_bounds, var.first);
          Expr extent = get_extent(bound);
          if(can_prove(2*var.second>=extent))   full_reuse[var.first]=1;
       //       cout<<st.first<<" "<<var.first<<" "<<var.second<<" ext "<<extent<<endl;
        }      
      }
          //bool is_function = (dep_analysis.env.find(prods.first) != dep_analysis.env.end());
          //bool is_same_stage=(prods.first==pipe_stages.first);
    }
    int sum=0;
    for(const auto &i:full_reuse){
       //   cout<<i.first<<" "<<i.second<<endl;
      if(i.second==1) sum++;
    }
    if(sum==(int)full_reuse.size()-1)  return 1;
    return 0;

  }
  /*
  map<string,Expr> Partitioner::find_min_tile_dims(const FStage &stg, pipe_IR p){
      map<string,Expr> min_tiles;
      map<string,Expr> min_tile;
      set<string> group_members;
      for (const auto &st : p.pipe_f) {
          group_members.insert(st.func.name());
       //   cout<<"member "<<st.func.name()<<endl;
      }
      set<string> parents = get_parents(stg.func, stg.stage_num);
      for(const auto &pipe_stages:p.pipe){
          for(const auto &prods : pipe_stages.second.re){
              bool is_function = (dep_analysis.env.find(prods.first) != dep_analysis.env.end());
              bool is_same_stage=(prods.first==pipe_stages.first);
              bool is_member=group_members.find(prods.first)!=group_members.end();
              bool is_parent = parents.find(prods.first)!=parents.end();
              if(!is_function||is_same_stage||!is_member||!is_parent) continue;
              cout<<"Producer "<<prods.first<<std::endl;
              for(const auto &ov : prods.second){
                      if(ov.first==p.pipe[stg.func.name()].cols[0])   continue;
                      if(!min_tiles[ov.first].defined())  min_tiles[ov.first]=ov.second;
                      else if(can_prove(min_tiles[ov.first]<ov.second))   min_tiles[ov.first]=ov.second;
                      cout<<"Dim "<<ov.first<<" overlap "<<ov.second<<std::endl;
                  }
              }
          }
          for(const auto &mins : min_tiles){
                  min_tile[mins.first]=cast(Int(32),mins.second);
           //       min_tile[mins.first]=make_zero(Int(32));
                  cout<<"Dim "<<mins.first<<" min tile "<<min_tile[mins.first]<<std::endl;
              
          }
          min_tile[p.pipe[stg.func.name()].cols[0]]=make_zero(Int(32));
      return min_tile;
  }*/

  map<string,Expr> Partitioner::find_min_tile_dims(const FStage &stg, pipe_IR p){
    map<string,Expr> min_tiles;
    map<string,Expr> min_tile;
    set<string> group_members;
    for (const auto &st : p.pipe_f) {
      if(p.pipe.find(st.func.name())!=p.pipe.end())    group_members.insert(st.func.name());
     //     cout<<"member "<<st.func.name()<<endl;
    }

    for(const auto &pipe_stages:p.pipe_f){
      if(p.pipe.find(pipe_stages.func.name())==p.pipe.end())  continue;
      if(p.pipe[pipe_stages.func.name()].is_inline) continue;
      //cout<<"consumer "<<pipe_stages.func.name()<<endl;
      set<string> parents = get_parents(pipe_stages.func, pipe_stages.stage_num);
      for(const auto &prods : parents){
        bool is_function = (dep_analysis.env.find(prods) != dep_analysis.env.end());
      //        bool is_same_stage=(prods==pipe_stages.func.name());
        if(p.pipe.find(prods)==p.pipe.end())  continue;
        bool is_member=group_members.find(prods)!=group_members.end();
       // if(!is_function||!is_member) continue;
        if(!is_function||!is_member) continue;
        if(p.pipe.find(pipe_stages.func.name())==p.pipe.end())  continue;
     //   cout<<"Producer "<<prods<<std::endl;
        for(const auto &ov : p.pipe[pipe_stages.func.name()].re[prods]){
          set<string> parents = get_parents(stg.func, stg.stage_num);
          if(ov.first==p.pipe[stg.func.name()].cols[0])   continue;
          if(!min_tiles[ov.first].defined())  min_tiles[ov.first]=ov.second;
          else if(can_prove(min_tiles[ov.first]<ov.second))   min_tiles[ov.first]=ov.second;
        //  cout<<"Dim "<<ov.first<<" overlap "<<ov.second<<std::endl;
       //   cout<<"Dim "<<ov.first<<" min tile "<<min_tiles[ov.first]<<endl;
        }
      }
    }
    for(const auto &mins : min_tiles){
     // if(!min_tile[mins.first].defined()) min_tile[mins.first]=make_zero(Int(32));
     if(mins.second.defined())  min_tile[mins.first]=cast(Int(32),mins.second);
        //  cout<<"Dim "<<mins.first<<" min tile "<<min_tile[mins.first]<<std::endl;    
   }
   min_tile[p.pipe[stg.func.name()].cols[0]]=make_zero(Int(32));
   return min_tile;
  }

  vector<string> Partitioner::find_prods(const set<string>&prods){
    vector<string> producers;
    for(const auto &pr:prods){
      producers.push_back(pr);
    }
    return producers;
  }

  map<string,map<string, Expr>> Partitioner::evaluate_reuse(const FStage &stg,
    const set<string> &prods) {
    map<string,map<string, Expr>> reuse;
    Function f = stg.func;

      // TODO: Check if tile size of 1 in each dimension gives a reasonable
      // answer or reuse should be evaluated at a much larger granularity or
      // symbolically. Using a symbolic version might be better if the objective
      // is to prove the dimension has no reuse. The only downside with the
      // symbolic method is that it is totally at the mercy of the simplifier.
      // Another option is sampling or using a larger granularity.
    map<string, Expr> tile_sizes;

    const vector<Dim> &dims = get_stage_dims(stg.func, stg.stage_num);
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      tile_sizes[dims[d].var] = 2;
    }

    DimBounds bounds = get_bounds_from_tile_sizes(stg, tile_sizes);
    //DimBounds stg_bounds = get_bounds(stg);
    //map<string,Expr> extents= bounds_to_estimates(stg_bounds);
    vector<map<string, Box>> reuse_regions =
    dep_analysis.overlap_regions(stg.func, stg.stage_num, bounds, prods,
     false, &costs.input_estimates);

    for (int d = 0; d < (int)dims.size() - 1; d++) {
      Expr total_reuse = make_zero(Int(32));
        //  if (debug::debug_level() >= 3) {
        //      disp_regions(reuse_regions[d]);
         // }
      for (const auto &reg : reuse_regions[d]) {
        Expr size = box_size(reg.second);
        if (!size.defined()) {
          total_reuse = Expr();
          break;
        } else {
              //    ////cout<<reg.first<<" "<<size<<std::endl;
          total_reuse += size;
         //if(!dims[d].is_rvar()) 
          reuse[reg.first].emplace(dims[d].var,simplify(size));
       //  else reuse[reg.first].emplace(dims[d].var,extents[dims[d].var]);
        }
      }
          //reuse.emplace(dims[d].var, simplify(total_reuse));
    }

    return reuse;
  }

  vector<pair<Partitioner::GroupingChoice, Partitioner::GroupConfig>>
  Partitioner::choose_candidate_grouping(const vector<pair<string, string>> &cands,
   Partitioner::Level level) {
    vector<pair<GroupingChoice, GroupConfig>> best_grouping;
    Expr best_benefit = make_zero(Int(64));
    for (const auto &p : cands) {
          // Compute the aggregate benefit of inlining into all the children.
      vector<pair<GroupingChoice, GroupConfig>> grouping;

      const Function &prod_f = get_element(dep_analysis.env, p.first);
      int final_stage = prod_f.updates().size();

      FStage prod(prod_f, final_stage);

      for (const FStage &c : get_element(children, prod)) {
        GroupConfig best_config;
        GroupingChoice cand_choice(prod_f.name(), c);

              // Check if the candidate has been evaluated for grouping before
        const auto &iter = grouping_cache.find(cand_choice);
        if (iter != grouping_cache.end()) {
          best_config = iter->second;
        } else {
          best_config = evaluate_choice(cand_choice, level);
                  // Cache the result of the evaluation for the pair
          grouping_cache.emplace(cand_choice, best_config);
        }

        grouping.push_back(make_pair(cand_choice, best_config));
      }

      bool no_redundant_work = false;
      Expr overall_benefit = estimate_benefit(grouping, no_redundant_work, true);

      debug(3) << "Candidate grouping:\n";
      for (const auto &g : grouping) {
        debug(3) << "  " << g.first;
      }
      debug(3) << "Candidate benefit: " << overall_benefit << '\n';
          // TODO: The grouping process can be non-deterministic when the costs
          // of two choices are equal
      if (overall_benefit.defined() && can_prove(best_benefit < overall_benefit)) {
        best_grouping = grouping;
        best_benefit = overall_benefit;
      }
    }

    debug(3) << "\nBest grouping:\n";
    for (const auto &g : best_grouping) {
      debug(3) << "  " << g.first;
    }
    if (best_grouping.size() > 0) {
      debug(3) << "Best benefit: " << best_benefit << '\n';
    }

    return best_grouping;
  }

  inline bool operator==(const map<string, Expr> &m1, const map<string, Expr> &m2) {
    if (m1.size() != m2.size()) {
      return false;
    }
    for (const auto &it1 : m1) {
      const auto &it2 = m2.find(it1.first);
      if (it2 == m2.end()) {
        return false;
      } else if (!equal(it1.second, it2->second)) {
        return false;
      }
    }
    return true;
  }


  vector<map<string, Expr>> Partitioner::generate_tile_configs(const FStage &stg, pipe_IR p) {
      // TODO: This is a wart due to the cost model not taking vectorization
      // and pre-fetching into account. Ensuring the innermost dimension has
      // at least size of 64 gives enough values for vectorization and can help
      // with prefetching. This also interacts with the number of parallel tasks
      // that are generated.
    //  int min_inner_dim_size = 2;


    map<string,Expr> min_tiles=p.min_tiles;
    vector<string> tile_vars=dims_to_tile(stg,min_tiles);
    //cout<<"after dims to tile"<<endl;
    vector<int> size_variants1 = {32,64,128,256,512,1024,2048,4096};
    vector<int> size_variants2 = {2,4,8,16,32,64,128,256};
    vector<int> size_variants;
    if(tile_vars.size()>1)   size_variants=size_variants1;
    else size_variants=size_variants2;  
    vector<map<string, Expr>> tile_configs;

    DimBounds stg_bounds = get_bounds(stg);
   // cout<<"after bounds"<<endl;
    map<string,Expr> extents= bounds_to_estimates(stg_bounds);

      //ensure that we will be able to parallelize;
    /*bool small_extents=true;
    for(const auto &ex:tile_vars){
      if(can_prove(extents[ex]/arch_params.parallelism<1))  ensure_parallelism=false;
      if(can_prove(extents[ex]>=32))  small_extents=false;
    }
    if(small_extents) ensure_parallelism=false;*/
    if(tile_vars.size()>1){   
     // int* a = nullptr;   // Pointer to int, initialize to nothing.
      int n;           // Size needed for array
      n=tile_vars.size();      // Read in the size
      //a = new int[n];  // Allocate n ints and save ptr in a.
      map<int,Expr> tiles;
      //map<int,int> a;
      std::vector<int> a(n);
      for (int i=0; i<n; i++) {


        tiles[i]=extents[tile_vars[i]]/(arch_params.parallelism);
        while (can_prove(min_tiles[tile_vars[i]]>tiles[i])){
          tiles[i]*=2;
        }
        tiles[i]=simplify(tiles[i]);
     //   cout<<"var "<<tile_vars[i]<<"min tile "<<tiles[i]<<endl;
      }    
      int index=0;
      int depth=tile_vars.size();
      int max_int=size_variants.size();
      bool flag_iter=true;
      while(flag_iter){
      //main body
        map<string,Expr> tiling;
        for(size_t i=0;i<tile_vars.size();i++){
          tiling.emplace(tile_vars[i],simplify(min(tiles[i],extents[tile_vars[i]])));
        }
        if (!tiling.empty()) {
         bool is_duplicate =
         std::find_if(tile_configs.begin(), tile_configs.end(),
           [&tiling](const map<string, Expr> &m) { return (tiling == m);})
         != tile_configs.end();

         if ((!is_duplicate)) {
          tile_configs.push_back(tiling);
        }   
      }      
      //check iter
      a[index]++;
      
      //if(tile_vars.size()>2 && can_prove(tiles[index]<16))  tiles[index]=simplify(tiles[index]*2);
      tiles[index]=simplify(tiles[index]*2);
      while (a[index] == max_int)
      {
              // Overflow, we're done
        if (index == depth - 1)
        {
              //    ////cout<<"breaking"<<std::endl;
          flag_iter=false;
          break;
        }

        tiles[index]=(max(extents[tile_vars[index]]/(arch_params.parallelism),min_tiles[tile_vars[index]]));;
        a[index] = 0;
        index++;

        a[index]++;
        tiles[index]=simplify(tiles[index]*2);
          //    ////cout<<"a "<<a[index]<<" max "<<max<<" index "<<index<<" depth "<<depth<<std::endl;
      }
      index=0;
    };
  //delete [] a;  // When done, free memory pointed to by a.
  //a = nullptr;     // Clear a to prevent using invalid memory reference.
  }else{

   for (const auto &dim_size : size_variants) {
    map<string, Expr> tiling;
    tiling.emplace(tile_vars[0], dim_size);

    if (!tiling.empty()) {
      bool is_duplicate =
      std::find_if(tile_configs.begin(), tile_configs.end(),
        [&tiling](const map<string, Expr> &m) { return (tiling == m);})
      != tile_configs.end();

      if ((!is_duplicate)) {
        tile_configs.push_back(tiling);
      }   
    }
  }



  }   
  /*
      // Skewed tile configurations
      for (size_t i = 0; i < tile_vars.size(); i++) {
          for (const auto &dim_size : size_variants) {
              map<string, Expr> tiling;
              tiling.emplace(tile_vars[i],
                             (i == 0) ? std::max(dim_size, min_inner_dim_size): dim_size);
              for (size_t j = 0; j < tile_vars.size(); j++) {
                  if (j < i) {
                      tiling.emplace(tile_vars[j], size_variants[size_variants.size() - 1]);
                  } else if (j > i) {
                      tiling.emplace(tile_vars[j], size_variants[0]);
                  }
              }
              if (!tiling.empty()) {
                  bool is_duplicate =
                      std::find_if(tile_configs.begin(), tile_configs.end(),
                                  [&tiling](const map<string, Expr> &m) { return (tiling == m);})
                      != tile_configs.end();

                  if ((!is_duplicate)) {
                      tile_configs.push_back(tiling);
                  }   
              }
          }
      }*/
  /*
      // Almost square tile configurations
      for (const auto &dim_size : size_variants) {
          map<string, Expr> tiling;
          for (size_t j = 0; j < tile_vars.size(); j++) {
              tiling.emplace(tile_vars[j],
                             (j == 0) ? std::max(dim_size, min_inner_dim_size): dim_size);
          }
          if (!tiling.empty()) {
              bool is_duplicate =
                  std::find_if(tile_configs.begin(), tile_configs.end(),
                              [&tiling](const map<string, Expr> &m) { return (tiling == m);})
                  != tile_configs.end();
              if (!is_duplicate) {
                  tile_configs.push_back(tiling);
              }
          }
      }

      // Reorder tile configurations
      for (int i = 0; i < (1 << (tile_vars.size())); i++) {
          map<string, Expr> tiling;
          for (size_t j = 0; j < tile_vars.size(); j++) {
              if (((i >> (j)) & 1) == 1) {
                  if (j == 0) {
                      tiling.emplace(tile_vars[j], min_inner_dim_size);
                  } else {
                      tiling.emplace(tile_vars[j], 1);
                  }
              }
          }
          if (!tiling.empty()) {
              bool is_duplicate =
                  std::find_if(tile_configs.begin(), tile_configs.end(),
                              [&tiling](const map<string, Expr> &m) { return (tiling == m);})
                  != tile_configs.end();
              if (!is_duplicate) {
                  tile_configs.push_back(tiling);
              }
          }
      
  }
  */
      //vector<map<string, Expr>>
      /*for(auto &iter :tile_configs){
        for(auto &iti:iter){
          ////cout<<iti.first<<" "<<iti.second<<std::endl;
        }
        ////cout<<"============"<<std::endl;
      }*/
  return tile_configs;
  }





  vector<string> Partitioner::dims_to_tile(const FStage &stg, map<string,Expr> min_tiles){
    const vector<Dim> &dims = get_stage_dims(stg.func, stg.stage_num);

      // Get the dimensions that are going to be tiled in this stage.
      // Skipping rvars for now.

      //find which vars we want to  tile
      //cout<<"dims_to_tile"<<endl;
    vector<string> tile_vars_init;
    vector<string> tile_vars_intr;
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      if (!dims[d].is_rvar()) {
        tile_vars_init.push_back(dims[d].var);
      }
    }
      //see if we actually WANT to tile all of these dims
      //first find which have an extent of at least 32
    DimBounds stg_bounds=get_bounds(stg);
    vector<string> tile_vars1=tile_vars_init;
      //Print the bounds
    Expr max_extent=make_zero(Int(32));
    string max_var;

    for(auto &it1:tile_vars1){
      Interval &bound = get_element(stg_bounds, it1);
      Expr extent = get_extent(bound);
      internal_assert(extent.defined());
      if(can_prove(extent>=max_extent)){
        max_extent=extent;
        max_var=it1;
      //  cout<<it1<<" "<<extent<<std::endl;
      }
      if(can_prove(extent<=64)||can_prove(min_tiles[it1]>=extent))  {
          ////cout<<"Stage "<<stg.func.name()<<" var "<<it1<<" will not be tiled"<<std::endl;

      }
      else{
    //    ////cout<<"Stage "<<stg.func.name()<<" var "<<it1<<" will be tiled"<<std::endl;
        tile_vars_intr.push_back(it1);
      }
    }
    Expr max_extent2=make_zero(Int(32));
    string max_var2;
    vector<string> tile_vars2=tile_vars1;
      //erase the largest
    std::vector<string>::iterator it2=find(tile_vars2.begin(),tile_vars2.end(),max_var);
    tile_vars2.erase(it2);
    for(auto &it1:tile_vars2){
      Interval &bound = get_element(stg_bounds, it1);
      Expr extent = get_extent(bound);
      internal_assert(extent.defined());
      if(can_prove(extent>=max_extent2)){
        max_extent2=extent;
        max_var2=it1;
              //////cout<<it1<<" "<<extent<<std::endl;
      }       
    }
    vector<string> tile_vars;
      //if it's empty just tile the largest 2 dims
     // ////cout<<" Stage has "<<tile_vars1.size()<<" tiled dims"<<std::endl;
    /*if(((tile_vars_intr.size()==1)||(tile_vars_intr.size()==0)&&tile_vars_init.size()==2)
      &&tile_vars_init.size()>2) {
     cout<<"Stage "<<stg.func.name()<<" no vars above 32 so "<<max_var<<" and "<<max_var2<<" will be tiled"<<std::endl;
   tile_vars.push_back(max_var);
   tile_vars.push_back(max_var2);
  }*/
    if(((tile_vars_intr.size()==1)||(tile_vars_intr.size()==0) )) {
   //  cout<<"Stage "<<stg.func.name()<<" no vars above 32 so "<<max_var<<" will be tiled"<<std::endl;

     tile_vars.push_back(max_var);
   }
   else tile_vars=tile_vars_intr;
   return tile_vars;
  }



  pair<map<string, Expr>, Partitioner::GroupAnalysis>
  Partitioner::find_best_tile_config(const Group &g) {
      // Initialize to no tiling
    map<string, Expr> no_tile_config;
    Group no_tile = g;
    no_tile.tile_sizes = no_tile_config;

    bool show_analysis = false;
    GroupAnalysis no_tile_analysis = analyze_group(no_tile, show_analysis);

    GroupAnalysis best_analysis = no_tile_analysis;
    map<string, Expr> best_config = no_tile_config;
    if (!best_analysis.cost.defined()) {
      return make_pair(best_config, best_analysis);
    }

      // Generate tiling configurations
    vector<map<string, Expr>> configs = generate_tile_configs_old(g.output);

    Group best_group = g;
    for (const auto &config : configs) {
      Group new_group = g;
      new_group.tile_sizes = config;

      GroupAnalysis new_analysis = analyze_group(new_group, show_analysis);

      bool no_redundant_work = false;
      Expr benefit = estimate_benefit(best_analysis, new_analysis,
        no_redundant_work, true);

      if (show_analysis) {
        debug(0) << "Benefit relative to not tiling:" << benefit << '\n';
        debug(0) << "Best analysis:" << new_analysis;
        debug(0) << "No tile analysis:" << no_tile_analysis;
        debug(0)
        << "arith cost:" << cast<float>(new_analysis.cost.arith / no_tile_analysis.cost.arith)
        << ", mem cost:" << cast<float>(new_analysis.cost.memory / no_tile_analysis.cost.memory) << '\n';
      }

      if (benefit.defined() && can_prove(benefit >= 0)) {
        best_config = config;
        best_analysis = new_analysis;
        best_group = new_group;
      }
    }

    return make_pair(best_config, best_analysis);
  }



  pair<map<string, Expr>, Partitioner::GroupAnalysis>
  Partitioner::find_best_tile_config_new(const Group &g, pipe_IR p,bool l2_constraint) {
      // Initialize to no tiling
    //  cout<<"tiles"<<endl;
    map<string, Expr> no_tile_config;
    Group no_tile = g;
    no_tile.tile_sizes = no_tile_config;

    bool show_analysis = false;
      GroupAnalysis no_tile_analysis;// = analyze_group_new(no_tile, p, show_analysis);
      no_tile_analysis.cost.memory=make_const(Int(64),LONG_MAX);
      no_tile_analysis.cost.arith=make_const(Int(64),LONG_MAX);
      no_tile_analysis.parallelism=make_one(Int(64));
      GroupAnalysis best_analysis = no_tile_analysis;
      map<string, Expr> best_config = no_tile_config;
      if (!best_analysis.cost.defined()) {
        return make_pair(best_config, best_analysis);
      }

      // Generate tiling configurations
     // cout<<"gen tiles before"<<endl;
      vector<map<string, Expr>> configs = generate_tile_configs(g.output,p);
      //fcout<<"gen tiles done"<<endl;
      Group best_group = g;
      string col=get_expr_str(p.pipe[p.output_func].cols[0]);
      for (const auto &config : configs) {
        //skip configurations with no small col tile

      /*  Expr isize=make_const(Int(64),p.inter_order.size()-1);
        Expr inter_var=p.find_var(p.inter_order,isize);
        if(inter_var.defined()){
          string par_var=get_expr_str(inter_var);
          const auto bvsize=p.bounds.find(par_var);
          const auto &vsize=config.find(par_var);
        //cout<<"tile size for "<<vsize->first<<" is "<<vsize->second<<" and bound "<<b_pvar<<endl;
          if(bvsize->second.defined()&&vsize->second.defined()&&(vsize!=config.end())&&(bvsize!=p.bounds.end())&&
            can_prove(bvsize->second==vsize->second)) continue;
        }*/
        Group new_group = g;
        new_group.tile_sizes = config;
        p.tiles=config;
        GroupAnalysis new_analysis = analyze_group_new(new_group, p, show_analysis,false);
     //  cout<<"new cost "<<new_analysis.cost.memory<<" best "<<best_analysis.cost.memory<<endl;
        bool no_redundant_work = false;
        Expr benefit = estimate_benefit(best_analysis, new_analysis,
          no_redundant_work, true);

        //  if (show_analysis) {

          //   ////cout << "No tile analysis:" << no_tile_analysis;
              /*debug(0)
                  << "arith cost:" << cast<float>(new_analysis.cost.arith / no_tile_analysis.cost.arith)
                  << ", mem cost:" << cast<float>(new_analysis.cost.memory / no_tile_analysis.cost.memory) << '\n';*/
         // }
     //   if(new_analysis.l2_footprint.defined())  cout<<"L2 foot "<<(new_analysis.l2_footprint)<<endl;

        if(l2_constraint&&new_analysis.l2_footprint.defined()&&can_prove(new_analysis.l2_footprint>256*1024)) continue;
        if (benefit.defined() && can_prove(benefit >= 0)) {
    //    cout << "Benefit relative to best:" << benefit << '\n';
         //    ////cout << "new analysis:" << new_analysis;
          best_config = config;
          best_analysis = new_analysis;
          best_group = new_group;
        }
      }

      return make_pair(best_config, best_analysis);
    }


    void Partitioner::group(Partitioner::Level level) {
      bool fixpoint = false;
      while (!fixpoint) {
        Cost pre_merge = get_pipeline_cost();

        fixpoint = true;
        vector<pair<string, string>> cand;
        for (const pair<FStage, Group> &g : groups) {
          bool is_output = false;
          for (const Function &f : outputs) {
            if (g.first.func.name() == f.name()) {
              is_output = true;
              break;
            }
          }

              // All stages of a function are computed at a single location.
              // The last stage of the function represents the candidate choice
              // of grouping the function into a consumer.

          const Function &prod_f = get_element(dep_analysis.env, g.first.func.name());
          bool is_final_stage = (g.first.stage_num == prod_f.updates().size());

          if (is_output || !is_final_stage) {
            continue;
          }

          const auto &iter = children.find(g.first);
          if (iter != children.end()) {
                  // All the stages belonging to a function are considered to be a
                  // single child.
            set<string> child_groups;
            for (const FStage &s : iter->second) {
              child_groups.insert(s.func.name());
            }

            int num_children = child_groups.size();
                  // Only groups with a single child are considered for grouping
                  // when grouping for computing in tiles.
                  // TODO: The current scheduling model does not allow functions
                  // to be computed at different points.
            if ((num_children == 1) && (level == Partitioner::Level::FastMem)) {
              const string &prod_name = prod_f.name();
              const string &cons_name = (*child_groups.begin());
              cand.push_back(make_pair(prod_name, cons_name));
            } else if((level == Partitioner::Level::Inline) && prod_f.is_pure()) {
              const string &prod_name = prod_f.name();
              cand.push_back(make_pair(prod_name, ""));
            }
          }
        }

        debug(3) << "\n============================" << '\n';
        debug(3) << "Current grouping candidates:" << '\n';
        debug(3) << "============================" << '\n';
        for (size_t i = 0; i < cand.size(); ++i) {
          debug(3) << "{" << cand[i].first << ", " << cand[i].second << "}" << '\n';
        }

        vector<pair<GroupingChoice, GroupConfig>> best = choose_candidate_grouping(cand, level);
        if (best.empty()) {
          continue;
        } else {
          fixpoint = false;
        }

          // The following code makes the assumption that all the stages of a function
          // will be in the same group. 'choose_candidate_grouping' ensures that the
          // grouping choice being returned adheres to this constraint.
        const string &prod = best[0].first.prod;

        const Function &prod_f = get_element(dep_analysis.env, prod);
        size_t num_stages = prod_f.updates().size() + 1;

        FStage final_stage(prod_f, num_stages - 1);
        set<FStage> prod_group_children = get_element(children, final_stage);

          // Invalidate entries of the grouping cache
        set<GroupingChoice> invalid_keys;
        for (const auto &c : prod_group_children) {
          for (const auto &entry : grouping_cache) {
            if ((entry.first.prod == c.func.name()) || (entry.first.cons == c)) {
              invalid_keys.insert(entry.first);
            }
          }
        }
        for (const auto &key : invalid_keys) {
          grouping_cache.erase(key);
        }

        for (const auto &group : best) {
          internal_assert(group.first.prod == prod);
          merge_groups(group.first, group.second, level);
        }

        for (size_t s = 0; s < num_stages; s++) {
          FStage prod_group(prod_f, s);
          groups.erase(prod_group);
          group_costs.erase(prod_group);

              // Update the children mapping
          children.erase(prod_group);
          for (auto &f : children) {
            set<FStage> &cons = f.second;
            auto iter = cons.find(prod_group);
            if (iter != cons.end()) {
              cons.erase(iter);
                      // For a function with multiple stages, all the stages will
                      // be in the same group and the consumers of the function
                      // only depend on the last stage. Therefore, when the
                      // producer group has multiple stages, parents of the
                      // producers should point to the consumers of the last
                      // stage of the producer.
              cons.insert(prod_group_children.begin(), prod_group_children.end());
            }
          }
        }

        Cost post_merge = get_pipeline_cost();
        if (debug::debug_level() >= 3) {
          disp_pipeline_costs();
        }
      }
    }

    DimBounds Partitioner::get_bounds(const FStage &s) {
      DimBounds bounds;

      const vector<string> &args = s.func.args();
      for (size_t d = 0; d < args.size(); d++) {
        bounds[args[d]] = get_element(pipeline_bounds, s.func.name())[d];
      }

      return get_stage_bounds(s.func, s.stage_num, bounds);
    }

    DimBounds Partitioner::get_bounds_from_tile_sizes(const FStage &s,
      const map<string, Expr> &tile_sizes) {
      map<string, Interval> bounds;

      const map<string, Interval> &def_bounds = get_bounds(s);

      const vector<Dim> &dims = get_stage_dims(s.func, s.stage_num);

      for (int d = 0; d < (int)dims.size() - 1; d++) {
        string var = dims[d].var;
        //cout<<"var "
        const Interval &bound = get_element(def_bounds, var);
        const auto &iter = tile_sizes.find(var);
        if (iter != tile_sizes.end()) { 
          const Expr &size = iter->second;
              // Check if the bounds allow for tiling with the given tile size,
              // i.e. ensure at least 2 tiles
          Expr extent = get_extent(bound);
          internal_assert(extent.defined());
          if (can_prove(extent >= 2 * size)) {
                  // TODO: Maybe shift this to the center of the pipeline bound
            bounds[var] = Interval(0, simplify(size - 1));
          } else {
                  // If the dimension is too small, do not tile it and set the
                  // extent of the bounds to that of the dimension estimate
            bounds[var] = bound;
          }
        } else {
          bounds[var] = bound;
        }
      }

      return bounds;
    }

    Partitioner::GroupAnalysis Partitioner::analyze_group(const Group &g, bool show_analysis) {
      set<string> group_inputs;
      set<string> group_members;

      for (const auto &stg : g.members) {
        group_members.insert(stg.func.name());
        set<string> parents = get_parents(stg.func, stg.stage_num);
        for (const auto &c : parents) {
          bool is_member = false;
          for (const auto &m : g.members) {
            if (m.func.name() == c) {
              is_member = true;
              break;
            }
          }
          if (!is_member) {
            group_inputs.insert(c);
          }
        }
      }

      // Count the number of tiles
      Expr estimate_tiles = make_one(Int(64));
      Expr parallelism = 4*arch_params.parallelism;

      if (!g.output.func.has_extern_definition()) {
          // Get the definition corresponding to the group output
        Definition def = get_stage_definition(g.output.func, g.output.stage_num);
        const vector<Dim> &dims = def.schedule().dims();

        DimBounds stg_bounds = get_bounds(g.output);

        for (int d = 0; d < (int)dims.size() - 1; d++) {
          const string &var = dims[d].var;
          const auto &iter = g.tile_sizes.find(var);
          if (iter != g.tile_sizes.end()) {
            const Expr &size = iter->second;
            Expr extent = get_extent(get_element(stg_bounds, var));
            if (!extent.defined()) {
              return GroupAnalysis();
            }

            Expr dim_tiles = simplify((extent + size - 1) / size);
            estimate_tiles *= dim_tiles;
                  // Since all Vars are inherently parallelizable by construct, we
                  // only need to take RVars into account for the analysis.
            if (can_parallelize_rvar(var, g.output.func.name(), def)) {
              parallelism *= dim_tiles;
            }
          }
        }
      }

      // Get the regions of the pipeline required to compute a tile of the group
      DimBounds tile_bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);

      map<string, Box> alloc_regions = dep_analysis.regions_required(
        g.output.func, g.output.stage_num, tile_bounds, group_members, false, &costs.input_estimates);

      map<string, Box> compute_regions = dep_analysis.regions_required(
        g.output.func, g.output.stage_num, tile_bounds, group_members, true, &costs.input_estimates);

      map<string, Box> group_reg, prod_reg, input_reg;

      // Separating into regions that computed within the group and regions that
      // are input to the group
      for (const auto &reg : compute_regions) {
        if ((group_members.find(reg.first) != group_members.end()) &&
          (reg.first != g.output.func.name())) {
          group_reg.emplace(reg.first, reg.second);
      } else if (group_inputs.find(reg.first) != group_inputs.end()) {
        if (dep_analysis.env.find(reg.first) != dep_analysis.env.end()) {
          prod_reg.emplace(reg.first, reg.second);
        } else {
          input_reg.emplace(reg.first, reg.second);
        }
      }
    }

      // Aggregate costs for intermediate functions in a tile and the
      // tile output
    Cost tile_cost = costs.region_cost(group_reg, g.inlined);
    if (!tile_cost.defined()) {
      return GroupAnalysis();
    }

    Cost out_cost = costs.stage_region_cost(g.output.func.name(),
      g.output.stage_num,
      tile_bounds, g.inlined);
    if (!out_cost.defined()) {
      return GroupAnalysis();
    }

    for (const auto &reg : alloc_regions) {
      if (!box_size(reg.second).defined()) {
        return GroupAnalysis();
      }
    }

    Cost group_cost(simplify(tile_cost.arith + out_cost.arith),
      simplify(tile_cost.memory + out_cost.memory));

      // Detailed load costs for all the group intermediates
    map<string, Expr> group_load_costs =
    costs.detailed_load_costs(group_reg, g.inlined);

    map<string, Expr> out_load_costs =
    costs.stage_detailed_load_costs(g.output.func.name(),
      g.output.stage_num,
      tile_bounds, g.inlined);

    combine_load_costs(group_load_costs, out_load_costs);

    Box out_tile_extent;
    if (g.output.stage_num == 0) {
      const vector<string> &args = g.output.func.args();
      for (size_t d = 0; d < args.size(); d++) {
        const auto &iter = tile_bounds.find(args[d]);
        if (iter != tile_bounds.end()) {
          out_tile_extent.push_back(iter->second);
        } else {
          out_tile_extent.push_back(Interval());
        }
      }
    }

    Cost per_tile_cost(group_cost.arith, make_zero(Int(64)));

      // This is the old cost model; keeping it here for reference, for now.
      /*
      if (tile_inter_size > arch_params.l1_size) {
          // Conservative estimate of accesses to memory
          //per_tile_mem_cost = tile_inter_size;
          // Aggressive estimate of accesses to memory
          per_tile_mem_cost = tile_cost.second;
      } else {
          // The tile_input_size captures the region of the input
          // required to compute the tile. However, all of it many not be
          // accessed during the computation of the tile when the access
          // is sparse. A better estimate is given by the smaller of
          // the number of memory accesses and the region size
          per_tile_mem_cost = std::min(tile_input_size + tile_output_size,
                                       tile_cost.second);
      }*/

      // TODO: Use smooth step curve from Jon to better model cache behavior,
      // where each step corresponds to different cache level.
      //
      // The current cost model drops off linearly. Larger memory footprint is
      // penalized more than smaller memory footprint (since smaller one can fit
      // more in the cache). The cost is clamped at 'balance', which is roughly at
      // memory footprint equal to or larger than the last level cache size.

      // If 'model_reuse' is set, the cost model should take into account memory
      // reuse within the tile, e.g. matrix multiply reuses inputs multiple times.
      // TODO: Implement a better reuse model.
    bool model_reuse = false;

      // Linear dropoff
    Expr load_slope = cast<float>(arch_params.balance) / arch_params.last_level_cache_size;
    for (const auto &f_load : group_load_costs) {
      internal_assert(g.inlined.find(f_load.first) == g.inlined.end())
      << "Intermediates of inlined pure fuction \"" << f_load.first
      << "\" should not have been in the group_load_costs\n";

      const auto &alloc_reg = get_element(alloc_regions, f_load.first);

      Expr footprint;
      bool is_group_member = (group_members.find(f_load.first) != group_members.end());
      bool is_output = (f_load.first == g.output.func.name());

          // We use allocated region as conservative estimate of the footprint since
          // the loads could be from any random locations of the allocated regions.

      if (!is_output && is_group_member) {
        footprint = costs.region_size(f_load.first, alloc_reg);
      } else {
        Expr initial_footprint;
        const auto &f_load_pipeline_bounds = get_element(pipeline_bounds, f_load.first);

        bool is_function = (dep_analysis.env.find(f_load.first) != dep_analysis.env.end());
              if (!is_function) { // It is a load to some input buffer
                  // Initial loads
                initial_footprint = costs.input_region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
                footprint = costs.input_region_size(f_load.first, alloc_reg);
              } else if (is_output) { // Load to the output function of the group
                internal_assert(is_group_member)
                << "Output " << f_load.first << " should have been a group member\n";
                  // Initial loads
                initial_footprint = costs.region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
                footprint = costs.region_size(f_load.first, out_tile_extent);
              } else { // Load to some non-member function (i.e. function from other groups)
                  // Initial loads
                initial_footprint = costs.region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
                footprint = costs.region_size(f_load.first, alloc_reg);
              }

              if (model_reuse) {
                Expr initial_factor =
                cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
                per_tile_cost.memory += initial_factor * footprint;
              } else {
                footprint = initial_footprint;
              }

              if (!footprint.defined()) {
                return GroupAnalysis();
              }
            }

            Expr cost_factor = cast<int64_t>(min(1 + footprint * load_slope, arch_params.balance));
            per_tile_cost.memory += cost_factor * f_load.second;
          }

          if (show_analysis) {
            debug(0) << "\nDetailed loads:\n";
            for (const auto &f_load : group_load_costs) {
              debug(0) << "(" << f_load.first << "," << f_load.second << ")";
            }
            debug(0) << '\n';

            debug(0) << "\nPer tile memory cost:" << per_tile_cost.memory << '\n';
            debug(0) << "Per tile arith cost:" << per_tile_cost.arith << '\n';
          }

          GroupAnalysis g_analysis(
            Cost(per_tile_cost.arith * estimate_tiles, per_tile_cost.memory * estimate_tiles),
            parallelism);
          g_analysis.simplify();

          return g_analysis;
        }



        Partitioner::GroupAnalysis Partitioner::analyze_group_new(const Group &g, pipe_IR p, bool show_analysis,bool to_inline) {
          set<string> group_inputs;
          set<string> group_members;


    /*      cout<<"out of group "<<g.output<<" STNNN "<<g.output.stage_num<<endl;
          p.print_pipe();
          for(const auto &tilit:g.tile_sizes){
            cout<<tilit.first<<" "<<tilit.second<<std::endl;
          }
          for(const auto &mm:g.members) cout<<mm.func.name()<<endl;*/


          map<string,Expr> temp_tiles=g.tile_sizes;
     //     cout<<"before bounds"<<endl;
          DimBounds stg_bounds = get_bounds(g.output);
       //   cout<<"after bounds"<<endl;
          const vector<Dim> &dims = get_stage_dims(g.output.func, g.output.stage_num);
          for (int d = 0; d < (int)dims.size() - 1; d++) {
            if(temp_tiles.find(dims[d].var)==temp_tiles.end()){
              Expr extent = get_extent(get_element(stg_bounds, dims[d].var));
          //    cout<<" var "<<dims[d].var<<" not tiled setting the tile to "<<endl;
              if(p.intra_order.find(dims[d].var)==p.intra_order.end()) temp_tiles[dims[d].var] = 1;
              else temp_tiles[dims[d].var]=extent;
            }
          //  cout<<temp_tiles[dims[d].var]<<endl;
          }
          if(!to_inline){
            const auto &csize=temp_tiles.find(p.pipe[p.output_func].cols[0]);
            const auto &bsize=p.bounds.find(p.pipe[p.output_func].cols[0]);

            if(bsize!=p.bounds.end()&&can_prove(bsize->second>=256)&&
              csize!=temp_tiles.end()&&can_prove(csize->second<=128)) return GroupAnalysis();
          }
        for (const auto &stg : g.members) {
          group_members.insert(stg.func.name());
          set<string> parents = get_parents(stg.func, stg.stage_num);
          for (const auto &c : parents) {
            bool is_member = false;
            for (const auto &m : g.members) {
              if (m.func.name() == c) {
                is_member = true;
                break;
              }
            }
            if (!is_member) {
              group_inputs.insert(c);
            }
          }
        }
        //  cout<<"before estimating parallelism"<<endl;
      // Count the number of tiles
        Expr estimate_tiles = make_one(Int(64));
        for(const auto &tiles:g.tile_sizes){
          DimBounds stg_bounds = get_bounds(g.output);
          Expr extent = get_extent(get_element(stg_bounds, tiles.first));
          if(!extent.defined()) return GroupAnalysis();
          const Expr &size = tiles.second;
          Expr dim_tiles = simplify((extent + size - 1) / size);
          estimate_tiles*=dim_tiles;

        }

        Expr parallelism = 4*arch_params.parallelism;
        map<string,Expr> inter_tile_parallelism;
        if (!g.output.func.has_extern_definition()&&(!to_inline)) {
          // Get the definition corresponding to the group output
          Definition def = get_stage_definition(g.output.func, g.output.stage_num);


          DimBounds stg_bounds = get_bounds(g.output);
          Expr isize=make_const(Int(64),p.inter_order.size()-1);
          Expr inter_var=p.find_var(p.inter_order,isize);
          string par_var=get_expr_str(inter_var);
          //  cout<<"inter var "<<par_var<<endl;
          Expr extent = get_extent(get_element(stg_bounds, par_var));
          if (!extent.defined()) {
            return GroupAnalysis();
          }
          Expr dim_tiles=extent;
          const auto &iter = g.tile_sizes.find(par_var);
          if(iter!=g.tile_sizes.end()){ 
            const Expr &size = iter->second;
            dim_tiles = simplify((extent + size - 1) / size);
          }

          if (can_parallelize_rvar(par_var, g.output.func.name(), def)) {
            inter_tile_parallelism.emplace(par_var,dim_tiles);

          }

          //check if we have 2 tiled outer dims (usually up to two, can extend later)
          if(p.inter_order.size()>1){
            isize=make_const(Int(64),p.inter_order.size()-2);
            inter_var=p.find_var(p.inter_order,isize);
            par_var=get_expr_str(inter_var);
         //     cout<<"Par var 2 "<<par_var<<endl;
            extent = get_extent(get_element(stg_bounds, par_var));
        //      cout<<"ext "<<extent<<endl;
            if (!extent.defined()) {
              return GroupAnalysis();
            }

            const auto &iter1 = g.tile_sizes.find(par_var);
            if(iter1!=g.tile_sizes.end()){

              const auto &size1 = iter1->second;

              dim_tiles = simplify((extent + size1 - 1) / size1);
              bool will_be_tiled=(can_prove(extent>size1)||iter1==g.tile_sizes.end());

              if (can_parallelize_rvar(par_var, g.output.func.name(), def)&&will_be_tiled) {
                inter_tile_parallelism.emplace(par_var,dim_tiles);
              }
            }
            else{
              if (can_parallelize_rvar(par_var, g.output.func.name(), def)) {
                inter_tile_parallelism.emplace(par_var,extent);
              }
            }
          }
          /*
          stg_bounds = get_bounds(g.output);
          isize=make_const(Int(64),p.inter_order.size()-2);
          Expr inter_outer=p.find_var(p.inter_order,isize);
          string par_var_outer=get_expr_str(inter_outer);
          //<<inter_outer.str();
          for (const auto &inter_tile_vars:p.inter_order) {
              const string &var = inter_tile_vars.first;
              const auto &iter = g.tile_sizes.find(var);
              if (iter != g.tile_sizes.end()) {
                  const Expr &size = iter->second;
                  Expr extent = get_extent(get_element(stg_bounds, var));
                  if (!extent.defined()) {
                      return GroupAnalysis();
                  }

                  Expr dim_tiles = simplify((extent + size - 1) / size);
                  estimate_tiles *= dim_tiles;
                  bool will_be_tiled=can_prove(extent>size);
                  // Since all Vars are inherently parallelizable by construct, we
                  // only need to take RVars into account for the analysis.
                  //////cout<<"var "<<var<<" "<<par_var<<std::endl;
                 
                  if (can_parallelize_rvar(var, g.output.func.name(), def)&&will_be_tiled) {
                      inter_tile_parallelism.emplace(var,dim_tiles);
                      //parallelism = dim_tiles;
                      cout<<"Par "<<var<<" "<<inter_tile_parallelism[var]<<std::endl;
                  }
              }
          }*/
          //now find the min par dim
          bool at_least_one_tiled=false;
          for(const auto &par_vars:inter_tile_parallelism){
            bool is_tiled = g.tile_sizes.find(par_vars.first)!=g.tile_sizes.end();
            if(is_tiled)  at_least_one_tiled=true;  
            if(can_prove(parallelism>par_vars.second)&&is_tiled)  parallelism=par_vars.second;
          }
          if(!at_least_one_tiled) parallelism=make_one(Int(64));
        //    cout<<"parallelism "<<simplify(parallelism)<<endl;
        }

      // Get the regions of the pipeline required to compute a tile of the group


        map<string, Expr> buffers;
        //cout<<"before tbounds"<<endl;
        DimBounds tile_bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
      //  cout<<"after tbounds"<<endl;
          //outer intra var
  //      p.print_pipe();

        Expr insize=make_const(Int(64),p.intra_order.size()-1);
        string outer_intra_var=get_expr_str(p.find_var(p.intra_order,insize));

        map<string,Expr> temp_gtiles=g.tile_sizes;
        temp_gtiles[outer_intra_var]=make_one(Int(32));
        DimBounds tile_bounds_folded = get_bounds_from_tile_sizes(g.output, temp_gtiles);
     //     double t4=current_time_ir();
      //  cout<<"before regs"<<endl;
        map<string, Box> compute_regions = dep_analysis.regions_required(
          g.output.func, g.output.stage_num, tile_bounds, group_members, true, &costs.input_estimates);       
        map<string, Box> alloc_regions = dep_analysis.regions_required(
          g.output.func, g.output.stage_num, tile_bounds, group_members, false, &costs.input_estimates);   
        map<string, Box> alloc_regions_folded = dep_analysis.regions_required(
          g.output.func, g.output.stage_num, tile_bounds_folded, group_members, false, &costs.input_estimates); 

        //cout<<"after regs"<<endl;
  //     p.print_pipe();
        for (const FStage &s : g.members) {
          string c_var;
          if(p.pipe[s.func.name()].is_inline) continue;
          if(s.func.name()==g.output.func.name())  continue;
       //   size_t num_stages = s.func.updates().size() + 1;
         // if(s.stage_num!=num_stages-1)  continue;
      //    cout<<"stage "<<s.func.name()<<" "<<s.stage_num<<" "<<p.pipe[s.func.name()].stage_num<<endl;
          const vector<Dim> &dims = get_stage_dims(s.func, s.stage_num);
      
          string memb=s.func.name();
          c_var=get_expr_str(p.pipe[memb].compute.second);
      
          map<string, Expr> tile_sizes;
          if(p.pipe[memb].compute_inter){
            const auto &iter = alloc_regions.find(s.func.name());
       
            if (iter != alloc_regions.end()) {

              const vector<string> &args = s.func.args();
              for (size_t arg = 0; arg < args.size(); arg++) {

                tile_sizes[args[arg]] = get_extent(iter->second[arg]);
              }

            }
          }
          else{
            const auto &iter = alloc_regions_folded.find(s.func.name());

            if (iter != alloc_regions_folded.end()) {
          
              const vector<string> &args = s.func.args();
              for (size_t arg = 0; arg < args.size(); arg++) {
               // cout<<args[arg]<<endl;
                tile_sizes[args[arg]] = get_extent(iter->second[arg]);
          
                //if(!p.pipe[memb].store_inter&&args[arg]==outer_intra_var) tile_sizes[args[arg]]=make_one(Int(32));
              }

            }

          }
 

          DimBounds  mem_bounds = get_bounds_from_tile_sizes(s, tile_sizes);
 
          
          map<string, Expr> stg_estimates = bounds_to_estimates(mem_bounds);
 
          Expr buffer=make_one(Int(64));
          for(const auto &iti:stg_estimates){
            bool is_iti_rvar=false;
            for(const auto dd:dims){
              if((dd.var==iti.first)&&(dd.is_rvar())) is_iti_rvar=true;
            }
            if(is_iti_rvar) continue;
            auto dim_in_tiles = p.intra_order.find(iti.first)==p.intra_order.end();
            auto dim_in_inter = p.inter_order.find(iti.first)!=p.inter_order.end();
            if(dim_in_tiles&&dim_in_inter)  continue;
    //               std::cout<<s.func.name()<<" "<<iti.first<<" "<<iti.second<<" cvar "<<c_var<<" outer intra "<<outer_intra_var<<std::endl;
            Expr next=iti.second;
            if(!next.defined()) cout<<"ERROR"<<endl;
            if(memb!=g.output.func.name()&&(!p.pipe[memb].compute_inter)&&(iti.first==outer_intra_var)){
              if((p.pipe[memb].store_inter)&&(!IsPowerOfTwo(next))){

                next=simplify(cast<int>( pow(2, ceil(log(iti.second)/log(2)))));
               //     cout<<"fold value in "<<iti.first<<" will be changed from "<<iti.second<<" to "<<next<<endl;
              }
            }
            buffer=buffer*next;
          }
          if(buffers.find(memb)!=buffers.end()) buffers[memb]=simplify(max(buffers[memb],4*buffer));
          else buffers[memb]=simplify((4*buffer));
         //     cout<<"memb "<<memb<<" "<<buffers[memb]<<endl;
        }





        map<string, Box> group_reg, prod_reg, input_reg;

      // Separating into regions that computed within the group and regions that
      // are input to the group
        for (const auto &reg : compute_regions) {
          if ((group_members.find(reg.first) != group_members.end()) &&
            (reg.first != g.output.func.name())) {
            group_reg.emplace(reg.first, reg.second);
      //        ////cout<<"reg "<<reg.first<<std::endl;
        } else if (group_inputs.find(reg.first) != group_inputs.end()) {
          if (dep_analysis.env.find(reg.first) != dep_analysis.env.end()) {
            prod_reg.emplace(reg.first, reg.second);
          } else {
            input_reg.emplace(reg.first, reg.second);
          }
        }
      }
   // //cout<<"DONE2"<<endl;
      // Aggregate costs for intermediate functions in a tile and the
      // tile output
      Cost tile_cost = costs.region_cost(group_reg, g.inlined);
   //   //cout<<"DONE3"<<endl;
      if (!tile_cost.defined()) {
        return GroupAnalysis();
      }

      Cost out_cost = costs.stage_region_cost(g.output.func.name(),
        g.output.stage_num,
        tile_bounds, g.inlined);

      if (!out_cost.defined()) {
        return GroupAnalysis();
      }

      /*for (const auto &reg : alloc_regions) {
          if (!box_size(reg.second).defined()) {
              return GroupAnalysis();
          }
      }*/

      Cost group_cost(simplify(tile_cost.arith + out_cost.arith),
        simplify(tile_cost.memory + out_cost.memory));

      // Detailed load costs for all the group intermediates
      map<string, Expr> group_load_costs =
      costs.detailed_load_costs(group_reg, g.inlined);
  
      map<string, Expr> out_load_costs =
      costs.stage_detailed_load_costs(g.output.func.name(),
        g.output.stage_num,
        tile_bounds, g.inlined);

      combine_load_costs(group_load_costs, out_load_costs);
  
      Box out_tile_extent;
      if (g.output.stage_num == 0) {
        const vector<string> &args = g.output.func.args();
        for (size_t d = 0; d < args.size(); d++) {
          const auto &iter = tile_bounds.find(args[d]);
          if (iter != tile_bounds.end()) {
            out_tile_extent.push_back(iter->second);
          } else {
            out_tile_extent.push_back(Interval());
          }
        }
      }
    ////cout<<"DONE3"<<endl;
      Cost per_tile_cost(group_cost.arith, make_zero(Int(64)));

      // This is the old cost model; keeping it here for reference, for now.
      /*
      if (tile_inter_size > arch_params.l1_size) {
          // Conservative estimate of accesses to memory
          //per_tile_mem_cost = tile_inter_size;
          // Aggressive estimate of accesses to memory
          per_tile_mem_cost = tile_cost.second;
      } else {
          // The tile_input_size captures the region of the input
          // required to compute the tile. However, all of it many not be
          // accessed during the computation of the tile when the access
          // is sparse. A better estimate is given by the smaller of
          // the number of memory accesses and the region size
          per_tile_mem_cost = std::min(tile_input_size + tile_output_size,
                                       tile_cost.second);
      }*/

      // TODO: Use smooth step curve from Jon to better model cache behavior,
      // where each step corresponds to different cache level.
      //
      // The current cost model drops off linearly. Larger memory footprint is
      // penalized more than smaller memory footprint (since smaller one can fit
      // more in the cache). The cost is clamped at 'balance', which is roughly at
      // memory footprint equal to or larger than the last level cache size.

      // If 'model_reuse' is set, the cost model should take into account memory
      // reuse within the tile, e.g. matrix multiply reuses inputs multiple times.
      // TODO: Implement a better reuse model.
     // bool model_reuse = false;
     // ////cout<<"false"<<std::endl;
      // Linear dropoff
      Expr partial_factor=make_zero(Float(64));
      Expr partial_footprint=make_zero(Float(64));
      Expr l2_footprint=make_zero(Float(64));
      map<string,Expr> footprints;
     //   //cout<<"DONE3"<<endl;
     // p.print_pipe();

      //double t1=current_time_ir();
      Expr load_slope = cast<float>(arch_params.balance) / arch_params.last_level_cache_size;
      for (const auto &f_load : group_load_costs) {
          //cout<<f_load.first<<std::endl;
        internal_assert(g.inlined.find(f_load.first) == g.inlined.end())
        << "Intermediates of inlined pure fuction \"" << f_load.first
        << "\" should not have been in the group_load_costs\n";
        //      ////cout<<"here will crash"<<std::endl;

        Expr footprint;
        Expr load_cost;

        bool is_group_member = (group_members.find(f_load.first) != group_members.end());
        bool is_output = (f_load.first == g.output.func.name());
        if(is_output)   continue;
        const auto &alloc_reg = get_element(alloc_regions, f_load.first);

        //   ////cout<<"here have crashed"<<std::endl;
          // We use allocated region as conservative estimate of the footprint since
          // the loads could be from any random locations of the allocated regions.

        if (!is_output && is_group_member) {
          if(p.pipe[f_load.first].is_inline)  continue;
           //   cout<<"mem "<<f_load.first<<endl;
          if(!to_inline)  footprint = buffers[f_load.first];
            //else footprint=costs.input_region_size(f_load.first, alloc_reg);
          else footprint = costs.region_size(f_load.first, alloc_reg);
          partial_footprint+=footprint;

  //            Expr cost_factor = cast<int64_t>(min(1 + footprint * load_slope, arch_params.balance));
        //     cout<<f_load.first<<" mem footprint "<<footprint<<endl;
          if((!p.pipe[f_load.first].store_inter))  l2_footprint+=footprint;
          load_cost = f_load.second;
       //       cout<<f_load.first<<" mem load cost "<<load_cost<<endl;
        //      cout<<f_load.first<<" mem load second "<<f_load.second<<endl;
       //       footprints.emplace(f_load.first,f_load.second/4);
          string f_col=p.pipe[g.output.func.name()].cols[0];
           // cout<<"mem "<<f_load.first<<" col "<<f_col<<endl;
          const auto &c_tile=temp_tiles.find(f_col);
          Expr cost_factor;
          if(can_prove(footprint>arch_params.last_level_cache_size))  cost_factor=arch_params.balance;
          else if(can_prove(footprint>256*1024))   cost_factor=make_const(Int(64),25);
          else if(can_prove(footprint>32*1024))   cost_factor=make_const(Int(64),10);
          else cost_factor=make_const(Int(64),1);
            if(!to_inline)  partial_factor+=load_cost*cost_factor/c_tile->second;//*min(1+footprint/arch_params.last_level_cache_size,40);
            else partial_factor+=load_cost*cost_factor;
          //    cout<<" mem "<<f_load.first<<" pfactor "<<simplify(partial_factor)<<endl;

          } else {
            Expr initial_footprint;

        //      const auto &f_load_pipeline_bounds = get_element(pipeline_bounds, f_load.first);

            bool is_function = (dep_analysis.env.find(f_load.first) != dep_analysis.env.end());
              if (!is_function) { // It is a load to some input buffer
                  // Initial loads
              //    cout<<"input "<<f_load.first<<endl;
                //  ////cout<<"here input"<<std::endl;
            //      initial_footprint = costs.input_region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
                initial_footprint = costs.input_region_size(f_load.first, alloc_reg);
                footprint=f_load.second;
           //       ////cout<<f_load.first<<" input footprint "<<f_load.second<<endl;
              //    load_cost = costs.region_size(f_load.first,comp_reg);
          //        ////cout<<f_load.first<<" input load cost "<<footprint<<endl;
                Expr cost_factor;
                if(can_prove(initial_footprint>arch_params.last_level_cache_size))  cost_factor=arch_params.balance;
                else if(can_prove(initial_footprint>256*1024))   cost_factor=make_const(Int(64),25);
                else if(can_prove(initial_footprint>32*1024))   cost_factor=make_const(Int(64),10);
                else cost_factor=make_const(Int(64),1);
                string f_col=p.pipe[g.output.func.name()].cols[0];
           //       cout<<"out col "<<f_col<<endl;
                const auto &c_tile=temp_tiles.find(f_col);
                  //Expr col_tile=temp_tiles[f_col];
              //    Expr cost_factor = cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
                if(!to_inline)   partial_factor+=(footprint/c_tile->second*cost_factor);
                else partial_factor+=(footprint*cost_factor);
           //     cout<<" inp pfactor "<<simplify(partial_factor)<<endl;
             //     partial_footprint+=simplify(footprint/c_tile->second);
              } else if (is_output) { // Load to the output function of the group
                internal_assert(is_group_member)
                << "Output " << f_load.first << " should have been a group member\n";
                  // Initial loads
               //   initial_footprint = costs.region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
              //   footprint = costs.region_size(f_load.first, out_tile_extent);
                footprint = make_zero(Int(64));
           //       ////cout<<"output footprint "<<f_load.second<<endl;
                partial_footprint+=footprint;
              } else { // Load to some non-member function (i.e. function from other groups)
                  // Initial loads
             //     cout<<"other group "<<f_load.first<<endl;
                  //find the column tile dimension
               string f_col=p.pipe[g.output.func.name()].cols[0];
               const auto &c_tile=temp_tiles.find(f_col);

               initial_footprint = costs.region_size(f_load.first, alloc_reg);
                  // Subsequent loads
               Expr cost_factor;
               if(can_prove(initial_footprint>arch_params.last_level_cache_size))  cost_factor=arch_params.balance;
               else if(can_prove(initial_footprint>256*1024))   cost_factor=make_const(Int(64),25);
               else if(can_prove(initial_footprint>32*1024))   cost_factor=make_const(Int(64),10);
               else cost_factor=make_const(Int(64),1);
               footprint=f_load.second;
           //     cout<<"non mem "<<f_load.first<<" out col "<<f_col<<endl;
                //  footprint = costs.region_size(f_load.first, alloc_reg);
          //      cout<<f_load.first<<" non mem footprint "<<footprint<<endl;
          //        load_cost = costs.region_size(f_load.first,comp_reg);
          //        ////cout<<f_load.first<<" non mem load cost "<<footprint<<endl;
             //     Expr cost_factor = cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
               if(!to_inline)   partial_factor+=(footprint/c_tile->second*cost_factor);
               else partial_factor+=(footprint*cost_factor);
           //    cout<<"non mem pfactor "<<simplify(partial_factor)<<endl;
             }

              /*if (model_reuse) {
                  Expr initial_factor =
                      cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
                  per_tile_cost.memory += initial_factor * footprint;
              } else {
                  footprint = initial_footprint;
              }*/

             if (!footprint.defined()) {
              return GroupAnalysis();
            }
          }

          //Expr cost_factor = cast<int64_t>(min(1 + footprint * load_slope, arch_params.balance));
          //per_tile_cost.memory += cost_factor * f_load.second;
        }
      //double t2=current_time_ir();
     // cout<<"time analyzing costs "<<t2-t1<<endl;
     /* if (show_analysis) {
          //cout << "\nDetailed loads:\n";
          for (const auto &f_load : group_load_costs) {
              //cout << "(" << f_load.first << "," << f_load.second << ")";
          }
          //cout << '\n';

          debug(0) << "\nPer tile memory cost:" << per_tile_cost.memory << '\n';
          debug(0) << "Per tile arith cost:" << per_tile_cost.arith << '\n';
      }*/
      //cout<<"l2 foot "<<simplify(l2_footprint)<<endl;


        GroupAnalysis g_analysis(
          Cost(per_tile_cost.arith * estimate_tiles,partial_factor * estimate_tiles),
          parallelism);
        g_analysis.l2_footprint=(l2_footprint);
        g_analysis.l3_footprint=partial_footprint;
        g_analysis.simplify();
      //  cout<<"total mem "<<g_analysis.cost.memory<<endl;
      //  cout<<"est tiles "<<estimate_tiles<<endl;
    //    cout<<"ended analysis"<<endl<<"==================================================="<<endl<<endl;;
        return g_analysis;
      }



      Partitioner::GroupAnalysis Partitioner::analyze_group_inline(const Group &g, pipe_IR p, bool show_analysis) {
        set<string> group_inputs;
        set<string> group_members;
      //find the parallelism vars

        bool compute_inter_exists=false;
        for(const auto sts:p.pipe){
          if(sts.second.compute_inter)  compute_inter_exists=true;
        }

     // for(const auto &tilit:g.tile_sizes){
          ////cout<<tilit.first<<" "<<tilit.second<<std::endl;
     // }
      //map<string,Expr> temp_tiles;
        for (const auto &stg : g.members) {
          group_members.insert(stg.func.name());
          set<string> parents = get_parents(stg.func, stg.stage_num);
          for (const auto &c : parents) {
            bool is_member = false;
            for (const auto &m : g.members) {
              if (m.func.name() == c) {
                is_member = true;
                break;
              }
            }
            if (!is_member) {
              group_inputs.insert(c);
            }
          }
        }

      // Count the number of tiles
        Expr estimate_tiles = make_one(Int(64));
        Expr parallelism = 4*arch_params.parallelism;
        map<string,Expr> inter_tile_parallelism;
        if (!g.output.func.has_extern_definition()) {
          // Get the definition corresponding to the group output
          Definition def = get_stage_definition(g.output.func, g.output.stage_num);
          const vector<Dim> &dims = def.schedule().dims();

          DimBounds stg_bounds = get_bounds(g.output);

          
          Expr isize=make_const(Int(64),p.inter_order.size()-1);
          Expr inter_outer=p.find_var(p.inter_order,isize);
          string par_var=get_expr_str(inter_outer);
          inter_tile_parallelism.emplace(par_var,make_one(Int(64)));
        //  cout<<"outer var "<<inter_outer<<std::endl;
          if(compute_inter_exists){
            isize=make_const(Int(64),p.inter_order.size()-2);
            inter_outer=p.find_var(p.inter_order,isize);
            string par_var=get_expr_str(inter_outer);
          //    cout<<"outer var "<<inter_outer<<std::endl;
            inter_tile_parallelism.emplace(par_var,make_one(Int(64)));
          }
          //<<inter_outer.str();
          for (int d = 0; d < (int)dims.size() - 1; d++) {
            const string &var = dims[d].var;
            const auto &iter = g.tile_sizes.find(var);
            if (iter != g.tile_sizes.end()) {
              const Expr &size = iter->second;
              Expr extent = get_extent(get_element(stg_bounds, var));
              if (!extent.defined()) {
                return GroupAnalysis();
              }

              Expr dim_tiles = simplify((extent + size - 1) / size);
              estimate_tiles *= dim_tiles;
                  // Since all Vars are inherently parallelizable by construct, we
                  // only need to take RVars into account for the analysis.
                  //////cout<<"var "<<var<<" "<<par_var<<std::endl;
              bool parallel_est=(inter_tile_parallelism.find(var)!=inter_tile_parallelism.end());
              if (can_parallelize_rvar(var, g.output.func.name(), def)&&parallel_est) {

                parallelism = dim_tiles;
                      ////cout<<"Par "<<par_var<<" "<<parallelism<<std::endl;
              }
            }
          }
          //now find the min par dim
          for(const auto &par_vars:inter_tile_parallelism){
            if(can_prove(parallelism<par_vars.second))  parallelism=par_vars.second;
          }
        }

      // Get the regions of the pipeline required to compute a tile of the group


        map<string, Box> alloc_regions;
     // map<string, Box> compute_regions;
        for(const auto &memb:group_members){
      //cout<<"mem "<<memb<<std::endl;
          DimBounds tile_bounds_compute = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
          map<string,Expr> temp_tiles=g.tile_sizes;
          if(memb!=g.output.func.name()){
            std::ostringstream ss;
            ss<<p.pipe[memb].compute.second;
            string c_var=ss.str();
            c_var.erase(std::remove(c_var.begin(), c_var.end(), '"'), c_var.end());
    //  ////cout<<" compute level "<<ss.str()<<std::endl;

     // const auto &ff=temp_tiles.find(ss);
            temp_tiles[c_var]=1;
          }
          DimBounds tile_bounds_alloc = get_bounds_from_tile_sizes(g.output, temp_tiles);
          map<string,Box> alloc_region;
          map<string,Box> compute_region;

          alloc_region= dep_analysis.regions_required(
            g.output.func, g.output.stage_num, tile_bounds_alloc, group_members, false, &costs.input_estimates);
          alloc_regions.emplace(memb,alloc_region[memb]);

      /*compute_region = dep_analysis.regions_required(
                    g.output.func, g.output.stage_num, tile_bounds_compute, group_members, true, &costs.input_estimates);
      compute_regions.emplace(memb,compute_region[memb]);*/
        }
        DimBounds tile_bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
        map<string, Box> compute_regions = dep_analysis.regions_required(
          g.output.func, g.output.stage_num, tile_bounds, group_members, true, &costs.input_estimates);

        for(const auto &inps:group_inputs){
      //////cout<<"inp "<<inps<<std::endl;
          DimBounds tile_bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
      //map<string,Expr> temp_tiles=g.tile_sizes;
          map<string,Box> alloc_region;  
          map<string,Box> compute_region;

          alloc_region= dep_analysis.regions_required(
            g.output.func, g.output.stage_num, tile_bounds, group_members, false, &costs.input_estimates);
          alloc_regions.emplace(inps,alloc_region[inps]);

      /*compute_region = dep_analysis.regions_required(
                    g.output.func, g.output.stage_num, tile_bounds, group_members, true, &costs.input_estimates);
      compute_regions.emplace(inps,compute_region[inps]);*/
        } 
   // //cout<<"DONE"<<endl;
  //group_inputs.insert(c);
  /*  for(const auto &regit:compute_regions){
      //cout<<"func "<<regit.first<<" box "<<regit.second<<endl;
    }*/


        map<string, Box> group_reg, prod_reg, input_reg;

      // Separating into regions that computed within the group and regions that
      // are input to the group
        for (const auto &reg : compute_regions) {
          if ((group_members.find(reg.first) != group_members.end()) &&
            (reg.first != g.output.func.name())) {
            group_reg.emplace(reg.first, reg.second);
      //        ////cout<<"reg "<<reg.first<<std::endl;
        } else if (group_inputs.find(reg.first) != group_inputs.end()) {
          if (dep_analysis.env.find(reg.first) != dep_analysis.env.end()) {
            prod_reg.emplace(reg.first, reg.second);
          } else {
            input_reg.emplace(reg.first, reg.second);
          }
        }
      }
   // //cout<<"DONE2"<<endl;
      // Aggregate costs for intermediate functions in a tile and the
      // tile output
      Cost tile_cost = costs.region_cost(group_reg, g.inlined);
   //   //cout<<"DONE3"<<endl;
      if (!tile_cost.defined()) {
        return GroupAnalysis();
      }

      Cost out_cost = costs.stage_region_cost(g.output.func.name(),
        g.output.stage_num,
        tile_bounds, g.inlined);
        //cout<<"DONE3"<<endl;
      if (!out_cost.defined()) {
        return GroupAnalysis();
      }

      for (const auto &reg : alloc_regions) {
        if (!box_size(reg.second).defined()) {
          return GroupAnalysis();
        }
      }

      Cost group_cost(simplify(tile_cost.arith + out_cost.arith),
        simplify(tile_cost.memory + out_cost.memory));

      // Detailed load costs for all the group intermediates
      map<string, Expr> group_load_costs =
      costs.detailed_load_costs(group_reg, g.inlined);
  ////cout<<"DONE3"<<endl;
      map<string, Expr> out_load_costs =
      costs.stage_detailed_load_costs(g.output.func.name(),
        g.output.stage_num,
        tile_bounds, g.inlined);

      combine_load_costs(group_load_costs, out_load_costs);
  ////cout<<"DONE4"<<endl;
      Box out_tile_extent;
      if (g.output.stage_num == 0) {
        const vector<string> &args = g.output.func.args();
        for (size_t d = 0; d < args.size(); d++) {
          const auto &iter = tile_bounds.find(args[d]);
          if (iter != tile_bounds.end()) {
            out_tile_extent.push_back(iter->second);
          } else {
            out_tile_extent.push_back(Interval());
          }
        }
      }
    ////cout<<"DONE3"<<endl;
      Cost per_tile_cost(group_cost.arith, make_zero(Int(64)));

      // This is the old cost model; keeping it here for reference, for now.
      /*
      if (tile_inter_size > arch_params.l1_size) {
          // Conservative estimate of accesses to memory
          //per_tile_mem_cost = tile_inter_size;
          // Aggressive estimate of accesses to memory
          per_tile_mem_cost = tile_cost.second;
      } else {
          // The tile_input_size captures the region of the input
          // required to compute the tile. However, all of it many not be
          // accessed during the computation of the tile when the access
          // is sparse. A better estimate is given by the smaller of
          // the number of memory accesses and the region size
          per_tile_mem_cost = std::min(tile_input_size + tile_output_size,
                                       tile_cost.second);
      }*/

      // TODO: Use smooth step curve from Jon to better model cache behavior,
      // where each step corresponds to different cache level.
      //
      // The current cost model drops off linearly. Larger memory footprint is
      // penalized more than smaller memory footprint (since smaller one can fit
      // more in the cache). The cost is clamped at 'balance', which is roughly at
      // memory footprint equal to or larger than the last level cache size.

      // If 'model_reuse' is set, the cost model should take into account memory
      // reuse within the tile, e.g. matrix multiply reuses inputs multiple times.
      // TODO: Implement a better reuse model.
      bool model_reuse = false;
     // ////cout<<"false"<<std::endl;
      // Linear dropoff
      Expr partial_factor=make_zero(Float(64));
      Expr partial_footprint=make_zero(Float(64));
      Expr l2_footprint=make_zero(Float(64));
      map<string,Expr> footprints;
     //   //cout<<"DONE3"<<endl;
      Expr load_slope = cast<float>(arch_params.balance) / arch_params.last_level_cache_size;
      for (const auto &f_load : group_load_costs) {
          //cout<<f_load.first<<std::endl;
        internal_assert(g.inlined.find(f_load.first) == g.inlined.end())
        << "Intermediates of inlined pure fuction \"" << f_load.first
        << "\" should not have been in the group_load_costs\n";
        //      ////cout<<"here will crash"<<std::endl;

        Expr footprint;
        Expr load_cost;

        bool is_group_member = (group_members.find(f_load.first) != group_members.end());
        bool is_output = (f_load.first == g.output.func.name());
        if(is_output)   continue;
        const auto &alloc_reg = get_element(alloc_regions, f_load.first);
        const auto &comp_reg = get_element(compute_regions, f_load.first);
        //   ////cout<<"here have crashed"<<std::endl;
          // We use allocated region as conservative estimate of the footprint since
          // the loads could be from any random locations of the allocated regions.

        if (!is_output && is_group_member) {
            //  cout<<"mem "<<f_load.first<<endl;
          footprint = costs.region_size(f_load.first, alloc_reg);

              ////cout<<f_load.first<<" mem footprint "<<footprint<<endl;
          if((!p.pipe[f_load.first].store_inter)&&(!p.pipe[f_load.first].is_inline))  l2_footprint+=footprint;
          load_cost = costs.region_size(f_load.first,comp_reg);
              ////cout<<f_load.first<<" mem load cost "<<load_cost<<endl;
           //   footprints.emplace(f_load.first,f_load.second/4);
          Expr cost_factor = cast<int64_t>(min(1 + footprint * load_slope, arch_params.balance));
          partial_factor+=f_load.second*cost_factor;
          partial_footprint+=footprint;
        } else {
          Expr initial_footprint;

          const auto &f_load_pipeline_bounds = get_element(pipeline_bounds, f_load.first);

          bool is_function = (dep_analysis.env.find(f_load.first) != dep_analysis.env.end());
              if (!is_function) { // It is a load to some input buffer
                  // Initial loads
              //    cout<<"input "<<f_load.first<<endl;
                //  ////cout<<"here input"<<std::endl;
                initial_footprint = costs.input_region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
                  //footprint = costs.input_region_size(f_load.first, alloc_reg);
                footprint=f_load.second;
           //       ////cout<<f_load.first<<" input footprint "<<f_load.second<<endl;
              //    load_cost = costs.region_size(f_load.first,comp_reg);
          //        ////cout<<f_load.first<<" input load cost "<<footprint<<endl;
                string f_col=p.pipe[g.output.func.name()].cols[0];
           //       //cout<<"col "<<f_col<<endl;
                const auto &c_tile=g.tile_sizes.find(f_col);
                  //Expr col_tile=g.tile_sizes[f_col];
                Expr cost_factor = cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
                partial_factor+=simplify(cost_factor*footprint);
                partial_footprint+=simplify(footprint/c_tile->second);
              } else if (is_output) { // Load to the output function of the group
                internal_assert(is_group_member)
                << "Output " << f_load.first << " should have been a group member\n";
                  // Initial loads
               //   initial_footprint = costs.region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
              //   footprint = costs.region_size(f_load.first, out_tile_extent);
                footprint = make_zero(Int(64));
           //       ////cout<<"output footprint "<<f_load.second<<endl;
                partial_footprint+=footprint;
              } else { // Load to some non-member function (i.e. function from other groups)
                  // Initial loads
             //     cout<<"other group "<<f_load.first<<endl;
                  //find the column tile dimension
               string f_col=p.pipe[g.output.func.name()].cols[0];
               const auto &c_tile=g.tile_sizes.find(f_col);

               initial_footprint = costs.region_size(f_load.first, f_load_pipeline_bounds);
                  // Subsequent loads
               footprint=f_load.second;
                //  footprint = costs.region_size(f_load.first, alloc_reg);
          //      cout<<f_load.first<<" non mem footprint "<<footprint<<endl;
          //        load_cost = costs.region_size(f_load.first,comp_reg);
          //        ////cout<<f_load.first<<" non mem load cost "<<footprint<<endl;
               Expr cost_factor = cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
               partial_factor+=simplify(cost_factor*footprint);
               partial_footprint+=(footprint/c_tile->second);
             }

             if (model_reuse) {
              Expr initial_factor =
              cast<int64_t>(min(1 + initial_footprint * load_slope, arch_params.balance));
              per_tile_cost.memory += initial_factor * footprint;
            } else {
              footprint = initial_footprint;
            }

            if (!footprint.defined()) {
              return GroupAnalysis();
            }
          }

          //Expr cost_factor = cast<int64_t>(min(1 + footprint * load_slope, arch_params.balance));
          //per_tile_cost.memory += cost_factor * f_load.second;
        }


        GroupAnalysis g_analysis(
          Cost(per_tile_cost.arith * estimate_tiles,partial_factor * estimate_tiles),
          parallelism);
      //g_analysis.footprints=footprints;
        g_analysis.simplify();
    //  ////cout<<"ended here"<<std::endl;
        return g_analysis;
      }



      Partitioner::Group Partitioner::merge_groups(const Group &prod_group,
       const Group &cons_group) {
        vector<FStage> group_members;
        for (const auto &s : prod_group.members) {
          group_members.push_back(s);
        }
        for (const auto &s : cons_group.members) {
          group_members.push_back(s);
        }

        Group group(cons_group.output, group_members);

        for (const auto &f : prod_group.inlined) {
          group.inlined.insert(f);
        }
        for (const auto &f : cons_group.inlined) {
          group.inlined.insert(f);
        }

        return group;
      }

      void Partitioner::merge_groups(const GroupingChoice &choice, const GroupConfig &eval,
       Partitioner::Level level) {
        const Function &prod_f = get_element(dep_analysis.env, choice.prod);
        size_t num_stages = prod_f.updates().size() + 1;

        const FStage &child = choice.cons;
        Group &child_group = get_element(groups, child);

        for (size_t s = 0; s < num_stages; s++) {
          FStage cand(prod_f, s);
          Group &cand_group = get_element(groups, cand);
          child_group.members.insert(child_group.members.end(),
           cand_group.members.begin(),
           cand_group.members.end());

          if (level == Partitioner::Level::Inline) {
            for (const auto &stg : cand_group.members) {
              child_group.inlined.insert(stg.func.name());
            }
          } else {
            for (const auto &in : cand_group.inlined) {
              child_group.inlined.insert(in);
            }
          }
        }

        child_group.tile_sizes = eval.tile_sizes;

      // Update group costs.
      // We could just reuse the analysis from 'eval' since it was computed
      // by assuming the merge had happened.
        group_costs[child] = eval.analysis;
      }

      Partitioner::GroupConfig Partitioner::evaluate_choice(const GroupingChoice &choice,
        Partitioner::Level level) {
      // Create a group that reflects the grouping choice and evaluate the cost
      // of the group.
        const Function &prod_f = get_element(dep_analysis.env, choice.prod);
        int num_prod_stages = prod_f.updates().size() + 1;
        vector<Group> prod_groups;

        for (int s = 0; s < num_prod_stages; s++) {
          FStage prod_s(prod_f, s);
          prod_groups.push_back(get_element(groups, prod_s));
        }

        Group cons = get_element(groups, choice.cons);
        Group group = cons;
        for (const auto &prod_g : prod_groups) {
          group = merge_groups(prod_g, group);
        }

        GroupAnalysis group_analysis;
        map<string, Expr> best_tile_config;

        if (level == Partitioner::Level::Inline) {
          // Set the tile sizes to one along all dimensions of the consumer group
          map<string, Expr> tile_sizes;

          const Function &cons_f = cons.output.func;

          const vector<Dim> &dims = get_stage_dims(cons_f, cons.output.stage_num);
          for (int d = 0; d < (int)dims.size() - 1; d++) {
            tile_sizes[dims[d].var] = 1;
          }

          group.tile_sizes = tile_sizes;

          for (const auto &prod_g : prod_groups) {
            for (const FStage &s : prod_g.members) {
              group.inlined.insert(s.func.name());
            }
          }

          for (const string &f : cons.inlined) {
            group.inlined.insert(f);
          }

          group_analysis = analyze_group(group, false);
          best_tile_config = tile_sizes;

        } else {
          pair<map<string, Expr>, GroupAnalysis> config = find_best_tile_config(group);
          best_tile_config = config.first;
          group_analysis = config.second;
        }

        return GroupConfig(best_tile_config, group_analysis);
      }

      Expr Partitioner::estimate_benefit(const GroupAnalysis &old_grouping,
       const GroupAnalysis &new_grouping,
       bool no_redundant_work,
       bool ensure_parallelism) {
      // TODO: Instead of having a hard parallelism constraint, it may be better
      // to consider other metric, such as arith_cost/parallelism
      //check if we can actually have enough parallelism
      //  if(new_grouping.parallelism.defined()&&can_prove(new_grouping.parallelism>=2*arch_params.parallelism)) return Expr();
        if (ensure_parallelism &&
          (!new_grouping.parallelism.defined() ||
           !can_prove(new_grouping.parallelism >= old_grouping.parallelism))) {

       //  cout<<"no par "<<new_grouping.parallelism<<endl;

         return Expr();
     }

     if (!old_grouping.cost.defined() || !new_grouping.cost.defined()) {
      cout<<"not defined cost"<<endl;
      return Expr();
    }

    Expr arith_benefit = old_grouping.cost.arith - new_grouping.cost.arith;
    if (no_redundant_work && !can_prove(arith_benefit >= 0)) {
      return Expr();
    }
    Expr mem_benefit = old_grouping.cost.memory - new_grouping.cost.memory;

     // 
    if(ensure_parallelism)  return simplify(mem_benefit);
    else {
      //  cout<<"old mem "<<(old_grouping.cost.memory)<<" old arith "<<(old_grouping.cost.arith)<<endl<<" new mem "<<(new_grouping.cost.memory)<<" new arith "<<(new_grouping.cost.arith)<<endl;
      return simplify(mem_benefit+arith_benefit);  
    } 
  }

  Expr Partitioner::estimate_benefit(
    const vector<pair<GroupingChoice, GroupConfig>> &new_grouping,
    bool no_redundant_work, bool ensure_parallelism) {

    set<FStage> old_groups;

    GroupAnalysis new_group_analysis(Cost(0, 0), Int(64).max());
    for (const auto &g : new_grouping) {
      const Function &prod_f = get_element(dep_analysis.env, g.first.prod);
      int num_prod_stages = prod_f.updates().size() + 1;
      for (int s = 0; s < num_prod_stages; s++) {
        FStage prod_s(prod_f, s);
        old_groups.insert(prod_s);
      }

      old_groups.insert(g.first.cons);

      GroupAnalysis analysisg = g.second.analysis;
      if (analysisg.defined()) {
        new_group_analysis.cost.arith += analysisg.cost.arith;
        new_group_analysis.cost.memory += analysisg.cost.memory;
        new_group_analysis.parallelism = min(new_group_analysis.parallelism,
         analysisg.parallelism);
      } else {
        new_group_analysis.cost = Cost();
        new_group_analysis.parallelism = Expr();
        break;
      }
    }
    new_group_analysis.simplify();

    GroupAnalysis old_group_analysis(Cost(0, 0), Int(64).max());
    for (const auto &g : old_groups) {
      const auto &iter = group_costs.find(g);
      internal_assert(iter != group_costs.end());
      GroupAnalysis analysisg = iter->second;
      if (analysisg.defined()) {
        old_group_analysis.cost.arith += analysisg.cost.arith;
        old_group_analysis.cost.memory += analysisg.cost.memory;
        old_group_analysis.parallelism = min(old_group_analysis.parallelism,
         analysisg.parallelism);
      } else {
        old_group_analysis.cost = Cost();
        old_group_analysis.parallelism = Expr();
        break;
      }
    }
    old_group_analysis.simplify();

    return estimate_benefit(old_group_analysis, new_group_analysis,
      no_redundant_work, ensure_parallelism);
  }

  map<string, Expr> Partitioner::bounds_to_estimates(const DimBounds &bounds) {
    map<string, Expr> estimates;
    for (const auto &bound : bounds) {
        //  //cout<<"b "<<bound.first<<" "<<get_extent(bound.second)<<endl;
      estimates.emplace(bound.first, get_extent(bound.second));
    }
    return estimates;
  }

  map<string, Box> Partitioner::group_storage_bounds(const Group &groups) {
    map<string, Box> group_storage_bounds;
  //    for (const pair<const FStage, Group> &gpair : groups) {
    const Group &g = groups;
    DimBounds bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
    //cout<<"tsizes done"<<endl;
    set<string> prods;
    for (const FStage &s : g.members) {
      prods.insert(s.func.name());
    }

    map<string, Box> reg_alloc =
    dep_analysis.regions_required(g.output.func, g.output.stage_num,
      bounds, prods, false, &costs.input_estimates);
    //cout<<"regs done"<<endl;
    map<string, Box> group_alloc;
    for (const FStage &s : g.members) {
      const auto &iter = reg_alloc.find(s.func.name());
      if ((iter != reg_alloc.end()) && (s.func.name() != g.output.func.name())) {
        group_alloc[s.func.name()] = iter->second;
      }
    }
//cout<<"gbounds done"<<endl;
    group_storage_bounds= group_alloc;
   //   }

    return group_storage_bounds;
  }

  map<FStage, DimBounds> Partitioner::group_loop_bounds(const Group &groups) {
    map<FStage, DimBounds> group_bounds;
    //  for (const pair<const FStage, Group> &gpair : groups) {
    Group g = groups;
    map<FStage, DimBounds> mem_bounds;

    DimBounds bounds = get_bounds_from_tile_sizes(g.output, g.tile_sizes);
      /*cout<<"bounds done "<<endl;
      if(g.members.size()==1){
        group_bounds[g.output]=bounds;
        return group_bounds;
      }*/
    set<string> prods;
    for (const FStage &s : g.members) {
      prods.insert(s.func.name());
    }

    map<string, Box> reg_computed =
    dep_analysis.regions_required(g.output.func, g.output.stage_num,
      bounds, prods, true, &costs.input_estimates);
        //  for(const auto &qq:reg_computed){
              //cout<<qq.first<<" "<<(qq.second)<<endl;
          //}
    for (const FStage &s : g.members) {
              //cout<<s.func.name()<<endl;
      const auto &iter = reg_computed.find(s.func.name());
      if (iter != reg_computed.end()) {
        map<string, Expr> tile_sizes;

        const vector<string> &args = s.func.args();
        for (size_t arg = 0; arg < args.size(); arg++) {
          tile_sizes[args[arg]] = get_extent(iter->second[arg]);
                      ////cout<<args[arg]<<" "<<get_extent(iter->second[arg])<<endl;

        }
        mem_bounds[s] = get_bounds_from_tile_sizes(s, tile_sizes);
      }
              //else //cout<<"not found iter "<<s.func.name()<<endl;
    }

    group_bounds= mem_bounds;


      //}

    return group_bounds;
  }

  // We need to get the base name of the dimension for scheduling (i.e. it
  // can't have any dots). For example, in split case, if "x" is the starting
  // dimension name, after split(x, x0, xi, ...), we will end up with something
  // like "x.x0" and  "x.xi". If we want to later schedule "x.x0", we need to
  // pass "x0" instead of "x.x0".
  string get_base_name(string name) {
    size_t dot_pos = name.rfind('.');
    if (dot_pos != string::npos) {
      return name.substr(dot_pos + 1);
    }
    return name;
  }

  // Return true if any of the values or args in 'def' refers to any of
  // the inputs or outputs, with access function which depends on 'var'.
  bool access_inputs_or_outputs(Definition def, VarOrRVar var,
    const map<string, Type> &inputs,
    const vector<Function> &outputs) {
    FindAllCalls find;
    def.accept(&find);

    for (size_t i = 0; i < find.call_args.size(); ++i) {
      const string &func = find.call_args[i].first;
      const vector<Expr> &args = find.call_args[i].second;

      if (inputs.find(func) == inputs.end()) {
              // Check if 'func' is an output
        bool is_output =
        std::find_if(outputs.begin(), outputs.end(),
          [&func](const Function &f) { return (f.name() == func);})
        != outputs.end();
        if (!is_output) {
                  // 'func' is neither an input or an output
          continue;
        }
      }

          // Check if any of the accesses to 'func' depends on 'var'
      for (const auto &arg : args) {
        if (expr_uses_var(arg, var.name())) {
          return true;
        }
      }
    }

    return false;
  }

  pair<VarOrRVar, VarOrRVar> Partitioner::split_dim(
    const Group &g, Stage f_handle, int stage_num, Definition def,
    bool is_group_output, VarOrRVar v, const Expr &factor, string in_suffix,
    string out_suffix, map<string, Expr> &estimates, AutoSchedule &sched) {
      // Create new variables for the split dimensions
    string arg_name = v.name();
    string inner_name = arg_name + in_suffix;
    string outer_name = arg_name + out_suffix;
    VarOrRVar inner(inner_name, v.is_rvar), outer(outer_name, v.is_rvar);

    {
      const auto &iter = sched.internal_vars.find(inner.name());
      if (iter == sched.internal_vars.end()) {
        sched.internal_vars.emplace(inner.name(), inner);
      } else {
        internal_assert(iter->second.is_rvar == inner.is_rvar);
      }
    }
    {
      const auto &iter = sched.internal_vars.find(outer.name());
      if (iter == sched.internal_vars.end()) {
        sched.internal_vars.emplace(outer.name(), outer);
      } else {
        internal_assert(iter->second.is_rvar == outer.is_rvar);
      }
    }

      // The default tail strategy is good enough for most use cases (see docs on
      // TailStrategy::Auto). However, the default of pure vars in update definitions
      // is RoundUp, which may introduces an out-of-bound error if it is an access
      // to inputs or outputs.
      //
      // We could have just used GuardWithIf when splitting pure vars in update
      // definition to ensure no out-of-bounds error. However, this is only
      // necessary, if the update definition involves accesses to inputs or outputs.
      // For other accesses, we could potentially use a more aggressive tail strategy
      // such as RoundUp or ShiftInwards. Note that if we use RoundUp or ShiftInwards,
      // any nested loops (generated by compute_at) will be affected as well. However,
      // since in the current auto-scheduler model, we always compute_at at the group
      // output, if the update definition is not the group output, we do not need to
      // care for the nested loops. If it is the update definition of the group output
      // however, we'd better make sure that no other member of the groups accesses
      // the inputs or outputs.
    TailStrategy strategy = TailStrategy::Auto;
    if ((stage_num > 0) && !v.is_rvar) {
      if (!is_group_output) {
        if (access_inputs_or_outputs(def, v, costs.inputs, outputs)) {
          strategy = TailStrategy::GuardWithIf;
        }
      } else {
        bool any_access_inputs_outputs = false;
        for (const FStage &mem : g.members) {
          if (mem.func.name() == f_handle.name()) {
            continue;
          }
          Definition mem_def = get_stage_definition(mem.func, mem.stage_num);
          if (access_inputs_or_outputs(mem_def, v, costs.inputs, outputs)) {
            any_access_inputs_outputs = true;
            break;
          }
        }
        if (any_access_inputs_outputs) {
          strategy = TailStrategy::GuardWithIf;
        }
      }
    }

    f_handle.split(v, outer, inner, factor, strategy);

    std::ostringstream oss;
    oss << "split(" << arg_name << ", " << outer_name << ", " << inner_name << ", " << factor;
    switch (strategy) {
      case TailStrategy::RoundUp:
      oss << ", TailStrategy::RoundUp)";
      break;
      case TailStrategy::GuardWithIf:
      oss << ", TailStrategy::GuardWithIf)";
      break;
      case TailStrategy::ShiftInwards:
      oss << ", TailStrategy::ShiftInwards)";
      break;
      case TailStrategy::Auto:
      oss << ")";
      break;
      default:
      internal_assert(false);
    }
    sched.push_schedule(f_handle.name(), stage_num, oss.str(),
      {arg_name, outer_name, inner_name});

    const Expr &est = get_element(estimates, arg_name);
    internal_assert(est.defined());

    estimates[inner_name] = factor;
    estimates[outer_name] = simplify((est + factor - 1) / factor);
    estimates.erase(arg_name);

    return make_pair(inner, outer);
  }

  void Partitioner::vectorize_stage(const Group &g, Stage f_handle, int stage_num,
    Definition def, Function func, bool is_group_output,
    const Target &t, set<string> &rvars,
    map<string, Expr> &estimates, AutoSchedule &sched, pipe_IR p) {
    vector<Dim> &dims = def.schedule().dims();
    int vec_dim_index = -1;

      // Set the vector length as the maximum of the natural vector size of all
      // values produced by the function.
    int vec_len = 0;
    for (const auto &type : func.output_types()) {
      vec_len = std::max(vec_len, t.natural_vector_size(type));
    }
    string dim_name_inner=p.pipe[p.output_func].cols[0]+"_i";
    for (int d = 0; d < (int) dims.size() - 1; d++) {
      string dim_name = get_base_name(dims[d].var);
      bool can_vectorize = true;
      bool found_index=false;

      //cout<<"vector of "<<p.output_func<<" is "<<p.pipe[p.output_func].cols[0]<<" "<<dim_name_inner<<endl;
      if(dim_name==p.pipe[p.output_func].cols[0]) found_index=true;
      else if (dim_name==dim_name_inner) found_index=true;
      if (rvars.find(dim_name) != rvars.end()) {
        can_vectorize = can_parallelize_rvar(dim_name, func.name(), def);
      }
      const auto &iter = estimates.find(dim_name);
      if ((iter != estimates.end()) && iter->second.defined()) {
        if (can_vectorize && can_prove(iter->second >= vec_len)&&found_index) {
          vec_dim_index = d;
          break;
        }
      }
    }

    if ((vec_dim_index >= 0)) {
      string vec_dim_name = get_base_name(dims[vec_dim_index].var);

      bool is_rvar = (rvars.find(vec_dim_name) != rvars.end());
      internal_assert(is_rvar == dims[vec_dim_index].is_rvar());

      VarOrRVar vec_var(vec_dim_name, is_rvar);
      pair<VarOrRVar, VarOrRVar> split_vars =
      split_dim(g, f_handle, stage_num, def, is_group_output, vec_var, vec_len,
        "_vi", "_vo", estimates, sched);

      f_handle.vectorize(split_vars.first);
      sched.push_schedule(f_handle.name(), stage_num,
        "vectorize(" + split_vars.first.name() + ")",
        {split_vars.first.name()});

      if (is_rvar) {
        rvars.erase(vec_dim_name);
        rvars.insert(split_vars.first.name());
        rvars.insert(split_vars.second.name());
      }

          // TODO: Reorder vector dim to innermost if it is the innermost
          // storage dimension of the func.
          //
          // TODO: Check if the warning is necessary.
      if (vec_dim_index > 0) {
        user_warning << "Outer dim vectorization of var \"" << vec_dim_name
        << "\" in function \"" << f_handle.name() << "\"\n";
      }
    }
  }

  // Return true if the vars/rvars in 'ordering' are in the same order as the
  // dim list.
  inline bool operator==(const vector<Dim> &dims, const vector<VarOrRVar> &ordering) {
      if (dims.size() != ordering.size() + 1) { // The dim list also contains '__outermost'
        return false;
    }
    for (size_t i = 0; i < ordering.size(); ++i) {
      if (dims[i].var != ordering[i].name()) {
        return false;
      }
    }
    return true;
  }

  // Return true if the vars/rvars in 'ordering' are not in the same order as the
  // dim list.
  inline bool operator!=(const vector<Dim> &dims, const vector<VarOrRVar> &ordering) {
    return !(dims == ordering);
  }

  void Partitioner::reorder_dims(Stage f_handle, int stage_num, Definition def,
   map<string, Expr> strides, AutoSchedule &sched,map<string,Expr> sbounds) {
    vector<Dim> &dims = def.schedule().dims();
     // cout<<f_handle.name()<<endl;
    internal_assert(dims.size() > 1);
    vector<pair<string, int>> order;
     // for(const auto &sb:sbounds) cout<<sb.first<<" "<<sb.second<<endl; 
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      internal_assert(strides.find(dims[d].var) != strides.end());
    }
      //put the small extent rdoms first
   //   int oo=0;
    for(int d=0;d<(int)dims.size()-1;d++){
      string var_name = get_base_name(dims[d].var);
     //   cout<<var_name<<endl;
      const auto &iter = sbounds.find(var_name);
      if(iter!=sbounds.end()&&can_prove(iter->second<4)&&(dims[d].is_rvar())){
        pair<string,int> lord(iter->first,d);

        order.push_back(lord);
        strides.erase(iter->first);
         // cout<<" order "<<iter->first<<" "<<oo<<endl;
      }
      //  else if(iter!=sbounds.end()) cout<<iter->first<<" "<<iter->second<<endl;
    }

      // Iterate until all the dimensions have been assigned an order
    while (strides.size() > 0) {
          // Find the pure dimension (can be vars or rvars) with the smallest stride
      bool found_pure_dim = false;
      Expr min_pure_stride = Int(64).max();
      string min_pure_var;
      int min_pure_index = -1;
      for (int d = 0; d < (int)dims.size() - 1; d++) {
        string var_name = get_base_name(dims[d].var);
        const auto &iter = strides.find(var_name);
        if ((iter != strides.end()) && dims[d].is_pure()) {
          const Expr &dim_stride = iter->second;
          internal_assert(dim_stride.defined());
          if (can_prove(dim_stride < min_pure_stride)) {
            min_pure_stride = dim_stride;
            min_pure_var = var_name;
            min_pure_index = d;
          }
          found_pure_dim = true;
        }
      }
      if (found_pure_dim && min_pure_var.empty()) {
              // Since none of the pure strides can be proven as the minimum, we
              // should break here otherwise it may cause infinite loop.
        return;
      }

          // Check if the stride of the pure dimension is smaller than
          // the first impure dimension that has not yet been assigned
          // an order
      Expr min_impure_stride = Int(64).max();
      string min_impure_var;
      int min_impure_index = -1;
      for (int d = 0; d < (int)dims.size() - 1; d++) {
        string var_name = get_base_name(dims[d].var);
        const auto &iter = strides.find(var_name);
        if ((iter != strides.end()) && !dims[d].is_pure()) {
          const Expr &dim_stride = iter->second;
          internal_assert(dim_stride.defined());
          if (can_prove(dim_stride < min_impure_stride)) {
            min_impure_stride = dim_stride;
            min_impure_var = var_name;
            min_impure_index = d;
                      // Impure dimensions cannot be reordered relative to
                      // each other. Stop after encountering the first impure
                      // dimension.
            break;
          }
        }
      }

      if (min_pure_var.empty() && min_impure_var.empty()) {
              // Since none of the pure and impure strides can be proven as the
              // minimum, we should break here otherwise it may cause infinite loop.
        return;
      }

      pair<string, int> curr_min_var;
      if (!min_impure_var.empty() && can_prove(min_impure_stride < min_pure_stride)) {
        curr_min_var.first = min_impure_var;
        curr_min_var.second = min_impure_index;
        internal_assert(dims[min_impure_index].is_rvar());
      } else {
        curr_min_var.first = min_pure_var;
        curr_min_var.second = min_pure_index;
      }
      bool already_set=false;
      for(const auto &iti:order){
        if(iti.first==curr_min_var.first) already_set=true;
      }
      if(!already_set){
        order.push_back(curr_min_var);
        strides.erase(curr_min_var.first);
      }
    }

    vector<VarOrRVar> ordering;
    for (const auto &o : order) {
      VarOrRVar o_var(o.first, dims[o.second].is_rvar());
       //   cout<<o.first<<endl;
      ordering.push_back(o_var);
    }

    internal_assert(!ordering.empty());
    set<string> var_list = {ordering[0].name()};
    string var_order = ordering[0].name();
    for (size_t o = 1; o < ordering.size(); o++) {
      var_order += ", " + ordering[o].name();
      var_list.insert(ordering[o].name());
    }

    //  if (dims != ordering) {
    f_handle.reorder(ordering);
    sched.push_schedule(f_handle.name(), stage_num, "reorder(" + var_order + ")", var_list);
     // }
  }

  // Visitor to find all the variables the depend on a variable.
  class FindVarsUsingVar : public IRVisitor {
    using IRVisitor::visit;

    void visit(const Let *let) override {
      if (expr_uses_vars(let->value, vars)) {
        vars.push(let->name);
      }
      let->value.accept(this);
      let->body.accept(this);
    }
    public :
    Scope<> vars;

    FindVarsUsingVar(string var) {
      vars.push(var);
    }
  };

  void Partitioner::generate_group_cpu_schedule(
    const Group &g, const Target &t,
    const map<FStage, DimBounds> &group_loop_bounds,
    const map<string, Box> &group_storage_bounds,
    const set<string> &inlines,
    AutoSchedule &sched, pipe_IR p, unsigned int out_st_num) {
    string out_f_name = g.output.func.name();
    Function g_out = g.output.func;

    debug(3) << "\n================\n";
    debug(3) << "Scheduling group:\n";
    debug(3) << "================\n";
    debug(3) << g;

    if (g.output.func.has_extern_definition()) {
      internal_assert(g.members.size() == 1);
      Func(g_out).compute_root();
      sched.push_schedule(g_out.name(), g.output.stage_num, "compute_root()", {});
      return;
    }
    if ((g.members.size()==1)||p.pipe.size()==1){
       //   cout<<g_out.name()<<" size 1 "<<endl;
      Func(g_out).compute_root();
      if(g.output.stage_num>0){
        Stage f_handle = Stage(Func(g_out));

        int stage_pure=g.output.stage_num-1;
        Func(g_out).compute_root();
        sched.push_schedule(f_handle.name(), stage_pure, "compute_root()", {});
      }
      else sched.push_schedule(g_out.name(), g.output.stage_num, "compute_root()", {});

      //return;
    }
      // Get the estimates for stage bounds
    DimBounds stg_bounds = get_bounds(g.output);
    map<string, Expr> stg_estimates = bounds_to_estimates(stg_bounds);

    Stage f_handle = Stage(Func(g_out));

      // Get a function handle for scheduling the stage
    if (g.output.stage_num > 0) {
        //  //cout<<"asdasdas"<<endl;
     // int stage_num = g.output.stage_num;
      int stage_pure=g.output.stage_num-1;
      Func(g_out).compute_root();
      sched.push_schedule(f_handle.name(), stage_pure, "compute_root()", {});
      f_handle = Func(g_out).update();
    } else {
      Func(g_out).compute_root();
      sched.push_schedule(f_handle.name(), g.output.stage_num, "compute_root()", {});
    }

      // Realize tiling and update the dimension estimates
    vector<VarOrRVar> outer_dims;
    set<string> outer_vars;
    vector<VarOrRVar> inner_dims;

      // Get the definition corresponding to the stage
    Definition def = get_stage_definition(g_out, out_st_num);

      // 'dims' will get modified since we are going to apply the schedules
      // (e.g. tiling, reordering, etc.)
    vector<Dim> &dims = def.schedule().dims();

      // Keep track of the rvars
    set<string> rvars;
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      if (dims[d].is_rvar()) {
        rvars.insert(get_base_name(dims[d].var));
      }
    }



    vector<string> dim_vars(dims.size() - 1);
    for (int d = 0; d < (int)dims.size() - 1; d++) {
      dim_vars[d] = get_base_name(dims[d].var);
    }
    map<string,Expr> tile_sizes=p.tiles;
    int non_tiled_inner_dims=0;
    int non_tiled_outer_dims=0;
      // Apply tiling to output of the group
    //p.print_pipe();
    if(p.pipe.size()>1){
    for (const auto &var : dim_vars) {
      bool is_rvar = (rvars.find(var) != rvars.end());
      VarOrRVar v(var, is_rvar);

      const auto &iter = tile_sizes.find(var);
      if ((iter != tile_sizes.end()) &&
        get_element(stg_estimates, var).defined() &&
        can_prove(get_element(stg_estimates, var) > iter->second)) {
        const Expr &tile_size = iter->second;
      if (can_prove(tile_size == 1)&&(var!=p.pipe[p.output_func].cols[0])) {
        outer_dims.push_back(v);
        outer_vars.insert(v.name());
     //   cout<<"outer dim"<<endl;
      } else {
        //for parallelism the split on the outer dim should be +1 if it's not mod 0
        const auto est=get_element(stg_estimates,var);
        Expr tile_sizef=tile_size;
        if(est.defined()){
        if(can_prove(est%tile_size!=0)&&(tile_sizes.size()>1)){
          cout<<"var "<<var <<"csize "<<est <<"tsize "<<tile_size<<endl;
          tile_sizef=simplify(tile_size+1);
          }
        }
        pair<VarOrRVar, VarOrRVar> tile_vars =
        split_dim(g, f_handle, g.output.stage_num, def, true, v,
          tile_sizef, "_i", "_o", stg_estimates, sched);

        inner_dims.push_back(tile_vars.first);
        //cout<<"inner dim "<<tile_vars.first.name()<<endl;
        outer_dims.push_back(tile_vars.second);
        //cout<<"outer dim "<<tile_vars.second.name()<<endl;
        outer_vars.insert(tile_vars.second.name());
        if (is_rvar) {
          rvars.erase(var);
          rvars.insert(tile_vars.first.name());
          rvars.insert(tile_vars.second.name());
        }
      }
    } else {

      bool is_intra=p.intra_order.find(v.var.name())!=p.intra_order.end();

    //  cout<<"v.var.name() "<<v.var.name()<<"intra "<<is_intra<<endl;
      if ((iter != tile_sizes.end()) &&
        get_element(stg_estimates, var).defined() &&
        can_prove(get_element(stg_estimates, var) <= iter->second)&&(is_intra)){

   //     cout<<"non tiled inner dim "<<v.name()<<endl;
        inner_dims.push_back(v);
      if(p.inter_order.find(v.name())!=p.inter_order.end())  non_tiled_outer_dims++;
    } 
    else  if(is_intra) {
   //   cout<<"non tiled inner dim "<<v.var<<endl;
      inner_dims.push_back(v);

      if(p.inter_order.find(v.name())!=p.inter_order.end())  non_tiled_outer_dims++;
       //         if(p.intra_order.find(v.name())!=p.intra_order.end())  non_tiled_inner_dims++;
    }
    else{
   //   cout<<"non tiled outer dim "<<v.var<<endl;  
      outer_dims.push_back(v);
      outer_vars.insert(v.name());
     //  if(p.inter_order.find(v.name())!=p.inter_order.end())  non_tiled_outer_dims++;
      if(p.intra_order.find(v.name())!=p.intra_order.end())  non_tiled_inner_dims++;
    }

  }
  }


      // Reorder the tile dimensions
 // p.print_pipe();
  if (!outer_dims.empty()) {
    vector<VarOrRVar> ordering;
    for(int order=0;order<(int)inner_dims.size();order++){
      for(const auto io:p.intra_order){
        string ss=io.first;
                  ////cout<<"ss "<<ss<<endl;
        string ssi=ss+"_i";
        Expr fixed_order=io.second;
        if(inner_dims.size()!=p.intra_order.size()) fixed_order=fixed_order-non_tiled_inner_dims;
        if(can_prove(fixed_order==order)){
       //  cout<<ss<<" "<<io.second<<endl;
         for(const auto &v:inner_dims){
          if((v.name()==ss)||(v.name()==ssi)){
     //       cout<<"inner "<<v.name()<<endl;
            ordering.push_back(v);
          }
        }
      }
    }
  }
   //       cout<<"outer dims "<<outer_dims.size()<<endl;
  //cout<<"non tiled inner dims "<<non_tiled_inner_dims<<endl;
  //cout<<"non tiled outer dims "<<non_tiled_outer_dims<<endl;
  for(int order=0;order<(int)outer_dims.size();order++){
    for(const auto oo:p.inter_order){
      string ss=oo.first;
      string ssi=ss+"_o";
      Expr fixed_order=oo.second;
      if(outer_dims.size()!=p.inter_order.size()) fixed_order=max(fixed_order-non_tiled_outer_dims,0) ;
      if(can_prove(fixed_order==order)){
      //  cout<<ss<<" "<<oo.second<<endl;
        for(const auto &v:outer_dims){
          if((v.name()==ss)||(v.name()==ssi)){
      //      cout<<"outer "<<v.name()<<endl;
            ordering.push_back(v);
          }
        }
      }
    }

  }



  set<string> var_list;
  string var_order = ordering[0].name();
  for (size_t o = 1; o < ordering.size(); o++) {
    var_order += ", " + ordering[o].name();
    var_list.insert(ordering[o].name());
  }

  if (dims != ordering) {
    f_handle.reorder(ordering);
    sched.push_schedule(f_handle.name(), g.output.stage_num,
      "reorder(" + var_order + ")", var_list);
  }
  }
  }
  int dims_before=get_stage_dims(g.output.func, g.output.stage_num).size();
  vectorize_stage(g, f_handle, g.output.stage_num, def, g_out, true, t,
    rvars, stg_estimates, sched,p);
  int dims_after=get_stage_dims(g.output.func, g.output.stage_num).size();
      // Parallelize definition
  Expr def_par = 1;
      // TODO: Investigate if it is better to pull one large dimension and
      // parallelize over it or to generate nested parallelism.
      //
      // Go from the outer to the innermost loop until sufficient parallelism
      // is achieved. Stop the search once we find a vectorized dimension since
      // it doesn't make any sense to have a parallelized inner loop within a
      // vectorized outer loop.
  bool nested_parallelism = true;
  int par_vars_already=0;
  if (nested_parallelism) {
    int dim_start = dims.size() - 2;
    string seq_var = "";
    for (int d = dim_start; d >= 0; d--) {
      if (dims[d].for_type == ForType::Vectorized) {
        break;
      }
      if (par_vars_already>1) break;

      string var = get_base_name(dims[d].var);
   //   cout<<"par "<<var<<endl;
              //string svar=get_expr_str(var);
      if(outer_vars.size()>0&&outer_vars.find(var)==outer_vars.end())  break;
      bool is_rvar = (rvars.find(var) != rvars.end());
      internal_assert(is_rvar == dims[d].is_rvar());
      VarOrRVar v(var, is_rvar);

      if (is_rvar && !can_parallelize_rvar(var, g_out.name(), def)) {
        if (seq_var == "") {
          seq_var = var;
        }
        continue;
      }

      if (can_prove(def_par >= arch_params.parallelism)) {
                  // Enough parallelism to saturate target machine
               //   break;
      }

      const auto &iter = stg_estimates.find(var);
      if ((iter != stg_estimates.end()) && iter->second.defined()) {
        if (seq_var != "") {
          VarOrRVar seq(seq_var, (rvars.find(seq_var) != rvars.end()));
          f_handle.reorder(seq, v);
          sched.push_schedule(f_handle.name(), g.output.stage_num,
            "reorder(" + seq_var + ", " + var + ")",
            {seq_var, var});
        }
        if(p.pipe.size()>1){
        f_handle.parallel(v);
        sched.push_schedule(f_handle.name(), g.output.stage_num,
          "parallel(" + var + ")", {var});
        }
        else{
          Expr pars=arch_params.parallelism;
          string parst=get_expr_str(pars);
                  f_handle.parallel(v);
        sched.push_schedule(f_handle.name(), g.output.stage_num,
          "parallel(" + var+","+parst + ")", {var,parst});
        break;

        }
        def_par = simplify(def_par * iter->second);
        par_vars_already++;
      } else {
        break;
      }
    }
  }

  if (can_prove(def_par < arch_params.parallelism)) {
    user_warning << "Insufficient parallelism for " << f_handle.name() << '\n';
  }
      ////cout<<"before compute_at"<<endl;
      // Find the level at which group members will be computed.
      //int tile_inner_index = dims.size() - outer_dims.size() - 1;
      //VarOrRVar tile_inner_var("", false);
      /*if (!outer_dims.empty()) {
          string var_name = get_base_name(dims[tile_inner_index].var);
          bool is_rvar = (rvars.find(var_name) != rvars.end());
          tile_inner_var = VarOrRVar(var_name, is_rvar);
      }*/
  vector<Dim> &dims_f = get_stage_dims(g.output.func, out_st_num);
  
  
  for (const FStage &mem : g.members) {
          // Skip member stages that have been inlined or stage that is the
          // output stage of the group

   
   bool is_function = (dep_analysis.env.find(mem.func.name()) != dep_analysis.env.end());
   if(!is_function) continue;
   //if(mem.is_image_param()) continue;
   if ((inlines.find(mem.func.name()) != inlines.end()) ||
    (mem.func.name() == g_out.name())) {
    //  cout<<"skipping "<<mem.func.name()<<endl;
    continue;
  }

          // Get the definition corresponding to the stage
  //cout<<"before def"<<endl;
  Definition mem_def = get_stage_definition(mem.func, mem.stage_num);

          // Get the estimates for the dimensions of the member stage
  //cout<<"before bounds"<<endl;
  //this is a bug with imparams that at the end get scheduled for some weird reason
 // if(group_loop_bounds.find(mem)==group_loop_bounds.end())  continue;
  map<string, Expr> mem_estimates =
  bounds_to_estimates(get_element(group_loop_bounds, mem));
  //        cout<<"failed bounds"<<endl;
  set<string> mem_rvars;
  vector<Dim> &mem_dims = mem_def.schedule().dims();
  for (int d = 0; d < (int)mem_dims.size() - 1; d++) {
    if (mem_dims[d].is_rvar()) {
      mem_rvars.insert(get_base_name(mem_dims[d].var));
    }
  }

          // Get a function handle for scheduling the stage
  Stage mem_handle = Stage(Func(mem.func));

  if (mem.stage_num > 0) {
    mem_handle = Func(mem.func).update(mem.stage_num - 1);
  } else {
              //find the compute/store vars
    VarOrRVar clevel("", false);
    VarOrRVar slevel("", false);
    ostringstream compute_level;
    ostringstream store_level;
    compute_level<<p.pipe[mem.func.name()].compute.second;
    string comp_level=compute_level.str();
    comp_level.erase(std::remove(comp_level.begin(), comp_level.end(), '"'), comp_level.end());
    store_level<<p.pipe[mem.func.name()].store.second;
    string stor_level=store_level.str();
    stor_level.erase(std::remove(stor_level.begin(), stor_level.end(), '"'), stor_level.end());

              //find store level
    if(p.pipe[mem.func.name()].store_inter){
             //     ////cout<<mem.func.name()<<" should be inter "<<endl;
      int tile_inner_index=dims_f.size()-1-outer_dims.size();
      string var_name = get_base_name(dims_f[tile_inner_index].var);
      stor_level=var_name;
    }
    else{
      int tile_inner_index;
      if(dims_before==dims_after)    tile_inner_index=inner_dims.size()-1;
      else tile_inner_index=inner_dims.size();
      string var_name = get_base_name(dims_f[tile_inner_index].var);
      stor_level=var_name;
    }
              //compute level
    if(p.pipe[mem.func.name()].compute_inter){
      int tile_inner_index=dims_f.size()-1-outer_dims.size();
      string var_name = get_base_name(dims_f[tile_inner_index].var);
      comp_level=var_name;
    }
    else{
      int tile_inner_index;
      if(dims_before==dims_after)    tile_inner_index=inner_dims.size()-1;
      else tile_inner_index=inner_dims.size();
      string var_name = get_base_name(dims_f[tile_inner_index].var);
      comp_level=var_name;
    }
    clevel = VarOrRVar(comp_level, false);
    slevel = VarOrRVar(stor_level, false);


              //if (!outer_dims.empty()) {

    Func(mem.func).compute_at(Func(g_out), clevel.var);
    Func(mem.func).store_at(Func(g_out), slevel.var);
  //  Func(mem.func).store_in(MemoryType::Stack);
  //  sched.push_schedule(mem_handle.name(), mem.stage_num,
   //   "store_in(MemoryType::Stack ",{});
            //sched.push_schedule(g_out.name(), g.output.stage_num, "compute_root()", {});
    string sanitized_g_out = get_sanitized_name(g_out.name());
    sched.push_schedule(mem_handle.name(), mem.stage_num,
      "compute_at(" + sanitized_g_out + ", " + comp_level + ")",
      {sanitized_g_out, comp_level});
    sched.push_schedule(mem_handle.name(), mem.stage_num,
      "store_at(" + sanitized_g_out + ", " + stor_level + ")",
      {sanitized_g_out, stor_level});
              /*} else {
                  user_warning << "Degenerate tiling. No dimensions are tiled" << '\n';
                  user_warning << "Computing \"" <<  mem.func.name() << "\" at root" << '\n';
                  Func(mem.func).compute_root();
                  sched.push_schedule(mem_handle.name(), mem.stage_num, "compute_root()", {});
              }*/
  }
  //cout<<"after compute_at"<<endl;
          // Reorder the dimensions for better spatial locality. If we only have
          // one dimension (excluding __outermost), there is nothing to reorder.
  if (dims.size() > 2) {
    map<string, Expr> mem_strides =
    analyze_spatial_locality(mem, group_storage_bounds, inlines);
    if (!mem_strides.empty()) {

                  //DimBounds stgbounds = 
    //  cout<<"before dims"<<endl;
      map<string,Expr> sbounds= find_dims(mem);
   //   cout<<"after dims"<<endl;
      reorder_dims(mem_handle, mem.stage_num, mem_def, mem_strides, sched,sbounds);
    //  cout<<"after reorder"<<endl;
    }
  }
  //cout<<"after spatial"<<endl;
  vectorize_stage(g, mem_handle, mem.stage_num, mem_def, mem.func, false,
    t, mem_rvars, mem_estimates, sched,p);
  //cout<<"finished vector"<<endl;
  }
  //cout<<"finished scheduling"<<endl;
  }

  void Partitioner::generate_cpu_schedule(const Target &t, AutoSchedule &sched, pipe_IR p) {
      // Grab the group bounds early as they rely on the dimensions of the group
      // outputs which will be altered by modifying schedules.
    Function f;
    
    int n_st=0;
    //cout<<"output "<<p.output_func<<endl;
   
    for(const auto &qq:p.pipe_f){
      if(qq.func.name()==p.output_func){
        if(qq.stage_num==p.pipe[qq.func.name()].stage_num){
          f=qq.func;
        
        n_st=qq.stage_num;
            //  break;
      }
      }

    }
    

    FStage output_stage(f,n_st);
    
    
    Group g(output_stage,p.pipe_f);
    map<string,Expr> no_tiles;
    //for(const auto &st:p.pipe_f)  cout<<"st.fun "<<st.func.name()<<endl;
    if(p.pipe.size()>1)  g.tile_sizes=p.tiles;
    else g.tile_sizes=no_tiles;
    
      //groups.emplace(output_stage,g);

    map<FStage, DimBounds> loop_bounds = group_loop_bounds(g);
    //cout<<"loop bounds done"<<endl;
    map<string, Box> storage_bounds = group_storage_bounds(g);



      //Function f=p.pipe_f[p.pipe_f.size()-1].func;
      //int n_st=p.pipe_f[p.pipe_f.size()-1].stage_num;

    set<string> inlines;
      // Mark all functions that are inlined.
      //for (const pair<FStage, Group> &g : groups) {
    for (const string &inline_func : g.inlined) {
          //    cout<<"inlining from inl_rest"<<inline_func<<endl;
      inlines.insert(inline_func);
    }
    for (const auto &stgs:p.pipe){
      if(stgs.second.is_inline)  {
            //    cout<<"inlining from opt_gran"<<stgs.first<<endl;
        inlines.insert(stgs.first);  
      } 
    }
    for (const auto &inl:inlines){
      if(inl!=p.output_func)  {
            //    cout<<"inlining from opt_gran"<<stgs.first<<endl;
        p.pipe.erase(inl);
      } 
    }
      //}

      // TODO: Inlining functions with update definitions has different
      // behavior than pure functions. They may need to be computed above
      // the innermost vector loop to avoid complications with varying
      // extents across different vector lanes.
      //
      // Since the default schedule is compute inline, we don't need to
      // explicitly call compute_inline() on the function.

      // Realize schedule for each group in the pipeline.
      //for (const auto &g : groups) {
    
    generate_group_cpu_schedule(g, t, loop_bounds,
      storage_bounds, inlines, sched, p,n_st);
      //}
  }

  Expr Partitioner::find_max_access_stride(const Scope<> &vars,
   const string &func_acc,
   const vector<Expr> &acc_exprs,
   const Box &buffer_bounds) {
    size_t num_storage_dims = 0;
    Expr bytes_per_ele = make_zero(Int(64));

      // Get the number of dimensions of the allocated storage and the
      // number of bytes required to store a single value of func_acc.
    const auto &iter = dep_analysis.env.find(func_acc);
    if (iter != dep_analysis.env.end()) {
      const Function &f = iter->second;
      for (const auto &e : f.values()) {
        bytes_per_ele += e.type().bytes();
      }
      num_storage_dims = f.schedule().storage_dims().size();
    } else {
      bytes_per_ele = get_element(costs.inputs, func_acc).bytes();
      num_storage_dims = buffer_bounds.size();
    }

    Expr curr_stride = bytes_per_ele;
    Expr stride = make_zero(Int(64));

    internal_assert(num_storage_dims <= acc_exprs.size());
    for (size_t sdim = 0; sdim < num_storage_dims; sdim++) {
          // Check if the access expression depends on any of the loop variables
          // in 'vars'. Expressions that do not involve the variable have stride 0.
      if (expr_uses_vars(acc_exprs[sdim], vars)) {
       stride = max(stride, curr_stride);
     }

     const Interval &dim_range = buffer_bounds[sdim];
     Expr dim_extent = get_extent(dim_range);
     if (!dim_extent.defined()) {
      return Expr();
    }
    curr_stride *= dim_extent;
  }

  return simplify(stride);
  }

  map<string, Expr>
  Partitioner::analyze_spatial_locality(const FStage &stg,
    const map<string, Box> &allocation_bounds,
    const set<string> &inlines) {
    internal_assert(!stg.func.has_extern_definition());
      // Handle inlining. When a function is inlined into another, the stride of
      // the accesses should be computed on the expression post inlining.
      // For example:
      // f(x, y) = ...;
      // g(x, y) = f(y, x); // transpose
      // h(x, y) = g(y, x); // transpose
      //
      // If both g and f are inlined into h, then the resulting expression for h
      // will look like:
      // h(x, y) = f(x, y);
      //
      // Computing the stride of a loop over x in the function h will be incorrect
      // if inlining is not taken into account.

      // Get all the allocations accessed in the definition corresponding to 'stg'.
    FindAllCalls find;
    Definition def = get_stage_definition(stg.func, stg.stage_num);
      // Perform inlining on the all the values and the args in the stage.
    for (auto &val : def.values()) {
      val = perform_inline(val, dep_analysis.env, inlines, dep_analysis.order);
    }
    for (auto &arg : def.args()) {
      arg = perform_inline(arg, dep_analysis.env, inlines, dep_analysis.order);
    }
    def.accept(&find);

      // Arguments on the left hand side might themselves involve accesses
      // to allocations and thus need to be accounted for when computing the
      // strides along each dimension.
    vector<pair<string, vector<Expr>>> &call_args = find.call_args;
      // Account for the spatial locality of the store. Add the access on the
      // left hand side to call_args.
    call_args.push_back(make_pair(stg.func.name(), def.args()));

      // Map for holding the strides across each dimension
    map<string, Expr> var_strides;
    const vector<Dim> &dims = def.schedule().dims();

    for (int d = 0; d < (int)dims.size() - 1; d++) {
          // Get all the variables involving the dimension in the definition.
      FindVarsUsingVar dep_vars(dims[d].var);
      def.accept(&dep_vars);

          // Accumulate the stride of each access to a loop dimension.
      Expr total_stride = 0;
      for (const pair<string, vector<Expr>> &call : call_args) {
        Box call_alloc_reg;
        const auto &iter = allocation_bounds.find(call.first);
        if (iter != allocation_bounds.end()) {
          call_alloc_reg = iter->second;
        } else {
          call_alloc_reg = get_element(pipeline_bounds, call.first);
        }
        Expr current_stride = find_max_access_stride(dep_vars.vars, call.first,
         call.second, call_alloc_reg);
        if (!current_stride.defined()) {
          return map<string, Expr>();
        }
        total_stride += current_stride;
      }
      var_strides.emplace(dims[d].var, simplify(total_stride));
    }

    return var_strides;
  }

  // Verify that function 'f' does not have partially specified schedules/bounds.
  // The current auto scheduler cannots handle such cases.
  void validate_no_partial_schedules(const Function &f) {
    if (f.has_extern_definition()) {
      return;
    }

      // Verify no compute_root or bounds are specified
    user_assert(f.schedule().compute_level().is_inlined())
    << "AutoSchedule: cannot auto-schedule function \"" << f.name()
    << "\" since it is scheduled to be computed at root\n";
    user_assert(f.schedule().bounds().empty())
    << "AutoSchedule: cannot auto-schedule function \"" << f.name()
    << "\" since it has partially specified bounds\n";

    int num_stages = f.updates().size() + 1;
    for (int stage = 0; stage < num_stages; ++stage) {
      const Definition &def = get_stage_definition(f, stage);
      const StageSchedule &schedule = def.schedule();

          // Verify no splits are specified
      user_assert(schedule.splits().empty())
      << "AutoSchedule: cannot auto-schedule function \"" << f.name()
      << "\" since it has partially specified schedules at stage " << stage << "\n";

          // Verify that none of the dimensions are scheduled to be parallelized or
          // vectorized, or unrolled.
      for (const auto &d : schedule.dims()) {
        user_assert(d.for_type == ForType::Serial)
        << "AutoSchedule: cannot auto-schedule function \"" << f.name()
        << "\" since stage " << stage << " is not serial at dim " << d.var << "\n";
      }

      if (stage == 0) {
              // Since we can only specialize on a Func, we only need to check for no
              // specializations for the initial stage.
        user_assert(def.specializations().empty())
        << "AutoSchedule: cannot auto-schedule function \"" << f.name()
        << "\" since it has specializations\n";

              // Verify that there is no loop reordering on the initial definition
              // (i.e. the Vars in the dim list should be in the same order as
              // the args in the LHS of the definition).
        internal_assert(schedule.dims().size() - 1 == def.args().size());
        for (size_t i = 0; i < def.args().size(); ++i) {
          const Variable *arg = def.args()[i].as<Variable>();
          internal_assert(arg);
          user_assert(arg->name == schedule.dims()[i].var)
          << "AutoSchedule: cannot auto-schedule function \"" << f.name()
          << "\" since dim \"" << arg->name << "\" at stage " << stage
          << " has been reordered\n";
        }
      } else {
              // Verify that there is no loop reordering on the update definition
              // (i.e. the Vars in the dim list should be in the same order as
              // the args in the LHS of the definition, the RVars in the dim list
              // should be in the same order as the RVars in the rvar list, and
              // all RVars should come before all Vars).

        const vector<Dim> &dims = schedule.dims();
        const vector<ReductionVariable> &rvars = schedule.rvars();
        const vector<Expr> &args = f.definition().args();
        internal_assert(dims.size() - 1 >= rvars.size());

        for (size_t i = 0; i < rvars.size(); ++i) {
          const Dim &d = dims[i];
          user_assert(d.is_rvar() && (d.var == rvars[i].var))
          << "AutoSchedule: cannot auto-schedule function \"" << f.name()
          << "\" since dim \"" << i << "\" at stage " << stage
          << " has been reordered\n";
        }

        internal_assert(dims.size() - rvars.size() - 1 <= args.size());
        int last_index = -1;
        for (int i = rvars.size(); i < (int)dims.size() - 1; ++i) {
          const Dim &d = dims[i];
          user_assert(!d.is_rvar())
          << "AutoSchedule: cannot auto-schedule function \"" << f.name()
          << "\" since dim \"" << i << "\" at stage " << stage
          << " has been reordered\n";

          const auto &iter =
          std::find_if(args.begin(), args.end(),
            [&d](const Expr &arg) {
              const Variable *v = arg.as<Variable>();
              return (d.var == v->name);
            });
          internal_assert(iter != args.end());
          int current_index = iter - args.begin();
          user_assert(current_index > last_index)
          << "AutoSchedule: cannot auto-schedule function \"" << f.name()
          << "\" since dim \"" << i << "\" at stage " << stage
          << " has been reordered\n";
          last_index = current_index;
        }
      }
    }
  }

  // If the cost of computing a Func is about the same as calling the Func,
  // inline the Func. Return true of any of the Funcs is inlined.
  bool inline_all_trivial_functions(const vector<Function> &outputs,
    const vector<string> &order,
    const map<string, Function> &env) {
    bool inlined = false;
      // The very last few functions in 'order' are the last to be realized in the
      // pipeline (the final producers) so there is no point in checking it.
    for (int i = 0; i < (int)order.size() - (int)outputs.size(); ++i) {
      bool is_output = false;
      for (const Function &f : outputs) {
        if (order[i] == f.name()) {
          is_output = true;
          break;
        }
      }
      if (is_output) {
              // Should not inline output Func
        debug(5) << "Skip inlining " << order[i] << " since it is an output\n";
        continue;
      }
      Function f1 = env.at(order[i]);
      if (is_func_trivial_to_inline(f1)) {
        inlined = true;
              ////cout << "Function \"" << order[i] << "\" is trivial to inline\n";
        for (int j = i + 1; j < (int)order.size() - (int)outputs.size(); ++j) {
          internal_assert(order[i] != order[j]);
          Function f2 = env.at(order[j]);

          if (f2.has_extern_definition() &&  !f1.is_wrapper()) {
            debug(5) << "Skip inlining of function \"" << f1.name()
            << "\" inside \"" << f2.name() << "\", because "
            << "non-wrapper functions cannot be inlined inside "
            << "extern functions.\n";
          } else {
            debug(5) << "Inline trivial function \"" << f1.name()
            << "\" inside \"" << f2.name() << "\"\n";
            inline_function(f2, f1);
          }
        }
      }
    }
    return inlined;
  }

  // Determine if a Func (order[index]) is only consumed by another single Func
  // in element-wise manner. If it is, return the name of the consumer Func;
  // otherwise, return an empty string.
  string is_func_called_element_wise(const vector<string> &order, size_t index,
   const map<string, Function> &env) {
    Function f1 = env.at(order[index]);
    if (f1.has_extern_definition() || !f1.can_be_inlined()) {
      return "";
    }
    internal_assert(index < order.size());

    string caller = "";
    for (size_t i = index + 1; i < order.size(); ++i) {
      Function f2 = env.at(order[i]);
      if (f2.has_extern_definition()) {
        continue;
      }
      int num_stages = f2.updates().size() + 1;
      for (int s = 0; s < num_stages; ++s) {
        Definition def = get_stage_definition(f2, s);
        FindAllCalls find;
        def.accept(&find);

        if (find.funcs_called.count(f1.name())) {
          if (caller.empty()) {
            caller = f2.name();
          } else {
                      // Found another caller of 'f1'
            return "";
          }
        }
        for (const auto &iter : find.call_args) {
          if (iter.first != f1.name()) {
            continue;
          }
          if (def.args().size() != iter.second.size()) {
                      // It's not an element-wise access
            return "";
          }
          for (size_t j = 0; j < iter.second.size(); ++j) {
            if (!equal(def.args()[j], iter.second[j])) {
                          // It's not an element-wise access
              return "";
            }
          }
        }
      }
    }
    return caller;
  }

  // Inline a Func if its values are only consumed by another single Func in
  // element-wise manner.
  bool inline_all_element_wise_functions(const vector<Function> &outputs,
   const vector<string> &order,
   const map<string, Function> &env) {
    bool inlined = false;
      // The very last few functions in 'order' are the last to be realized in the
      // pipeline (the final producers) so there is no point in checking it.
    for (int i = 0; i < (int)order.size() - (int)outputs.size(); ++i) {
      bool is_output = false;
      for (const Function &f : outputs) {
        if (order[i] == f.name()) {
          is_output = true;
          break;
        }
      }
      if (is_output) {
              // Should not inline output Func
        debug(5) << "Skip inlining " << order[i] << " since it is an output\n";
        continue;
      }
      string caller = is_func_called_element_wise(order, i, env);
      if (!caller.empty()) {
        inlined = true;
        debug(4) << "Inline function \"" << order[i] << "\" since it is called only by "
        << caller << " in element-wise manner\n";
        internal_assert(order[i] != caller);
        inline_function(env.at(caller), get_element(env, order[i]));
      }
    }
    return inlined;
  }

  // Return true if 'f' is used by some extern Func.
  bool used_by_extern_func(const map<string, Function> &env, const Function &f) {
    for (const auto &iter : env) {
      for (const ExternFuncArgument &arg : iter.second.extern_arguments()) {
        if (arg.is_func()) {
          if (Function(arg.func).name() == f.name()) {
            return true;
          }
        }
      }
    }
    return false;
  }

  // If the bounds of a Func are undefined, then we should just inline the Func
  // as long as it is legal to inline or used by some extern Func.
  set<string> get_unbounded_functions(const map<string, Box> &pipeline_bounds,
    const map<string, Function> &env) {
    set<string> unbounded;
    for (const auto &iter : env) {
      if (!pipeline_bounds.count(iter.first)) {
        debug(5) << "...Skip checking function \"" << iter.first
        << "\" since it does not have pipeline bounds\n";
        continue;
      }
      const Function &f = iter.second;
      if (!f.can_be_inlined() || used_by_extern_func(env, f)) {
        continue;
      }
      const Box &bound = get_element(pipeline_bounds, iter.first);
      if (is_box_unbounded(bound)) {
        unbounded.insert(iter.first);
      }
    }
    return unbounded;
  }

  bool inline_unbounded(const vector<Function> &outputs,
    const vector<string> &order,
    const map<string, Function> &env,
    const set<string> &unbounded) {
    bool inlined = false;
      // The very last few functions in 'order' are the last to be realized in the
      // pipeline (the final producers) so there is no point in checking it.
    for (int i = 0; i < (int)order.size() - (int)outputs.size(); ++i) {
      Function f1 = env.at(order[i]);
      if (!unbounded.count(f1.name())) {
        continue;
      }
      inlined = true;
      debug(4) << "Function \"" << order[i] << "\" is unbounded\n";
      for (int j = i + 1; j < (int)order.size(); ++j) {
        internal_assert(order[i] != order[j]);
        Function f2 = env.at(order[j]);
        debug(5) << "Inline unbounded function \"" << f1.name()
        << "\" inside \"" << f2.name() << "\"\n";
        inline_function(f2, f1);
      }
    }
    return inlined;
  }

  }  // anonymous namespace








  // Generate schedules for all functions in the pipeline required to compute the
  // outputs. This applies the schedules and returns a string representation of
  // the schedules. The target architecture is specified by 'target'.
  string generate_schedules(const vector<Function> &outputs, const Target &target,
    const MachineParams &arch_params) {
      // Make an environment map which is used throughout the auto scheduling process.
    map<string, Function> env;
    for (Function f : outputs) {
      map<string, Function> more_funcs = find_transitive_calls(f);
      env.insert(more_funcs.begin(), more_funcs.end());
    }

      // Finalize all the LoopLevels
    for (auto &iter : env) {
      iter.second.lock_loop_levels();
    }

      // Compute the topological order, before any trivial inlining (i.e. before
      // we remove any functions from 'env'). We need the full topological
      // order to pass to get_func() when generating the string representation
      // of the schedule.
    debug(2) << "Computing topological order...\n";
    vector<string> top_order = topological_order(outputs, env);

      // Validate that none of the functions in the pipeline have partial schedules.
    debug(2) << "Validating no partial schedules...\n";
    for (const auto &iter : env) {
      validate_no_partial_schedules(iter.second);
    }

      // The auto scheduling algorithm requires estimates on the outputs of the
      // pipeline to get quantitative estimates of costs for computing functions
      // in the pipeline.
    debug(2) << "Checking estimates on outputs...\n";
    check_estimates_on_outputs(outputs);

      // Run a pre-pass that inline all trivial Funcs (i.e. if the cost of
      // computing a Func is about the same as calling that Func, we should
      // just inline it).
    debug(2) << "Inlining all trivial functions...\n";
    if (inline_all_trivial_functions(outputs, top_order, env)) {
          // If any of the Funcs is inlined, we need to recompute 'env', since some
          // of the Funcs are no longer used and need to be removed from 'env'.
          //
          // Instead of recomputing 'env', we could also remove the inlined Func
          // within inline_all_trivial_functions(); however, it is a bit tricky
          // to do when dealing with inlined tuple. Consider the following case:
          //   f(x, y) = x + y;
          //   g(x, y) = {x, f(x, y)};
          //   h(x, y) = g(x, y)[0];
          // When 'g' is inlined in 'h', no one uses 'f' anymore and it can
          // be removed from 'env'. However, to know this, we need to trace
          // all the function calls within the pipeline. Thus, we might as well
          // recompute the 'env' from scratch.
      env.clear();
      for (Function f : outputs) {
        map<string, Function> more_funcs = find_transitive_calls(f);
        env.insert(more_funcs.begin(), more_funcs.end());
      }
    }

      // Compute the realization order of the functions within the pipeline.
    vector<string> order = realization_order(outputs, env).first;

      // Run a pre-pass that inline all Funcs which values are accessed by
      // another single Func in element-wise manner. We need to do this
      // repeatedly since some inlining decisions may enable further inlining
      // that previously not possible. Consider the following case:
      //   f1(x) = x;
      //   f2(x) = f1(x) + 2;
      //   f3(x) = f1(x) * 2;
      //   f4(x) = f2(x) + f3(x);
      //   f5(x) = f4(x) + 3;
      // In the first iteration, we cannot inline 'f1' since it is used by two
      // functions: 'f2' and 'f3'. If 'f2' and 'f4' get inlined and 'f3' is only
      // used by 'f4', then 'f1' can now also be inlined.
    debug(2) << "Inlining all element-wise functions...\n";
    while (inline_all_element_wise_functions(outputs, order, env)) {
          // We need to recompute 'env' for the same reason as with
          // inline_all_trivial_functions
      env.clear();
      for (Function f : outputs) {
        map<string, Function> more_funcs = find_transitive_calls(f);
        env.insert(more_funcs.begin(), more_funcs.end());
      }
      order = realization_order(outputs, env).first;
    }

      // Compute the bounds of function values which are used for dependence analysis.
    debug(2) << "Computing function value bounds...\n";
    FuncValueBounds func_val_bounds = compute_function_value_bounds(order, env);

      // Initialize the cost model.
      // Compute the expression costs for each function in the pipeline.
    debug(2) << "Initializing region costs...\n";
    RegionCosts costs(env, order);
    if (debug::debug_level() >= 3) {
      costs.disp_func_costs();
    }

    debug(2) << "Initializing dependence analysis...\n";
    DependenceAnalysis dep_analysis(env, order, func_val_bounds);

      // Compute bounds of all functions in the pipeline given estimates on
      // outputs. Also report functions which bounds could not be inferred.
    debug(2) << "Computing pipeline bounds...\n";
    map<string, Box> pipeline_bounds =
    get_pipeline_bounds(dep_analysis, outputs, &costs.input_estimates);

      // Determine all unbounded functions that are not extern Func or
      // used by some extern Funcs.
    debug(2) << "Determining all unbounded functions...\n";
    set<string> unbounded = get_unbounded_functions(pipeline_bounds, env);
    if (!unbounded.empty()) {
          // If some functions are unbounded, we should inline those directly.
          // Also, we need to recompute 'env' and re-initialize 'costs' and
          // 'dep_analysis'
      debug(2) << "Inlining all unbounded functions...\n";
      internal_assert(inline_unbounded(outputs, order, env, unbounded));

      env.clear();
      for (Function f : outputs) {
        map<string, Function> more_funcs = find_transitive_calls(f);
        env.insert(more_funcs.begin(), more_funcs.end());
      }
      order = realization_order(outputs, env).first;

      debug(2) << "Re-computing function value bounds...\n";
      func_val_bounds = compute_function_value_bounds(order, env);
      debug(2) << "Re-initializing region costs...\n";
      RegionCosts costs(env, order);
      debug(2) << "Re-initializing dependence analysis...\n";
      dep_analysis = DependenceAnalysis(env, order, func_val_bounds);
      debug(2) << "Re-computing pipeline bounds...\n";
      pipeline_bounds = get_pipeline_bounds(dep_analysis, outputs, &costs.input_estimates);
    }

    debug(2) << "Initializing partitioner...\n";
    Partitioner part(pipeline_bounds, arch_params, outputs, dep_analysis, costs);
      //create the pipeline
    pipe_IR p;
    unsigned int stage_ns=0;
    std::map<string,map<string,map<string, Expr>>> reuse_per_stage;
    set<string> wrappers;
    for (const auto &f : env) if(f.second.is_wrapper())  wrappers.insert(f.first);
    for (const auto &f : env) {
      FindAllCalls find;
      f.second.accept(&find);
      int num_stages = f.second.updates().size() + 1;
      map<string,Expr> svars;  
      set<string> srvars;  
      for (int s = 0; s < num_stages; s++) {
        FStage curr_s(f.second, s);
        map<string,map<string, Expr>> reuse = part.evaluate_reuse(curr_s, find.funcs_called);
        map<string,Expr> vars=part.find_dims(curr_s);
        vector<string> producers=part.find_prods(find.funcs_called);
        vector<Dim> &dims_s = get_stage_dims(curr_s.func, curr_s.stage_num);
              //find the first pure var
        string col_dim;
        for(const auto &dim_it:dims_s){
          if(!dim_it.is_rvar()) {
            col_dim=dim_it.var;
                  ////cout<<col_dim<<" col "<<endl;
            break;
          }
        }
        set<string> rvars;
        for(const auto &dim_it:dims_s){
          if(dim_it.is_rvar()) {
            rvars.insert(dim_it.var);
          }
        }
              string func_name=curr_s.func.name();//+"_"+to_string(s);
         //     cout<<"func_name"<<func_name<<endl;
              
        //      for(const auto &vv:vars)  cout<<vv.first<<" "<<vv.second<<endl;
              
             // bool only_update=true;
              bool only_inputs=true;
              //if((reuse.size()==1)&&(reuse.find(curr_s.func.name())==reuse.end()))  only_update=false;
              for(const auto &rr:reuse){
                bool is_function = (dep_analysis.env.find(rr.first) != dep_analysis.env.end());
                bool is_wrapper_func=(wrappers.find(rr.first)!=wrappers.end());
             //   cout<<"reuse of stage "<<curr_s.func.name()<<" update "<<s<<"  rr in  "<<rr.first<<endl;
                if((!is_wrapper_func&&(is_function)&&(rr.first!=curr_s.func.name()))) only_inputs=false;
                



              }
              if(!(only_inputs)){
              //  cout<<"reuse of stage "<<curr_s.func.name()<<" update "<<s<<"  put because "<<" "<<only_inputs<<endl;
           //    p.fill_stage(func_name,vars,rvars,producers,reuse,{col_dim},(curr_s.func.name()==outputs[0].name()),curr_s,s); 
           stage_ns=s; 
                reuse_per_stage.emplace(f.first,reuse);
                svars=vars;
                srvars=rvars;
              }
               if(num_stages==1)  stage_ns=0;
               p.fill_stage(func_name,vars,rvars,producers,reuse,{col_dim},(curr_s.func.name()==outputs[0].name()),curr_s,stage_ns);
        /*      else{
                p.pipe_f.push_back(curr_s);
                if((curr_s.func.name()==outputs[0].name())&&(s==num_stages-1)){
                  p.pipe[outputs[0].name()].stage_num=outputs[0].updates().size();
                  p.pipe[curr_s.func.name()].vars=vars;
                   p.pipe[curr_s.func.name()].rvars=rvars;
                }
           //    
                //p.pipe_f.push_back(curr_s);
       //         cout<<"reuse of stage "<<curr_s.func.name()<<" update "<<s<<" not put because "<<" "<<only_inputs<<endl;
              }*/

            }
            p.pipe[f.first].re=reuse_per_stage[f.first];
            p.pipe[f.first].vars=svars;
            p.pipe[f.first].rvars=srvars;
             
          }
          
        //find max reuse for each dimension to use as min for tile size constraint

          for(const auto &re : reuse_per_stage){
            cout<<"Stage "<<re.first<<std::endl;
            for(const auto &procs : re.second){
              cout<<"Producer "<<procs.first<<std::endl;
              for(const auto &ov : procs.second){
                cout<<"Dim "<<ov.first<<" overlap "<<ov.second<<std::endl;
              }
            }
          }
          vector<pipe_IR> pipe_without_luts=part.find_luts(env,reuse_per_stage,p);
          double t1=current_time_ir();
          vector<pipe_IR> opt_pipe=part.optimize_pipe(pipe_without_luts);
          double t2=current_time_ir();
          cout<<"time spent optimizing "<<(t2-t1)<<endl;
          AutoSchedule sched(env, top_order);
          //create the schedules
      //    cout<<"final pipes"<<endl;
      //    for(auto &gs:opt_pipe)  gs.print_pipe();
          for(const auto &gs:opt_pipe)  part.generate_cpu_schedule(target,sched,gs);
     ///       cout<<"must have finished"<<endl;
           std::ostringstream oss;
         oss << "// Target: " << target.to_string() << "\n";
         oss << "// MachineParams: " << arch_params.to_string() << "\n";
         oss << "\n";
         oss << sched;
         string sched_string = oss.str();
      //  string sched_string = "Done";
         cout<<sched_string<<endl;
         return sched_string;
       }

  }  // namespace Internal

  MachineParams MachineParams::generic() {
    return MachineParams(8, 8 * 1024 * 1024, 40);
  }

  std::string MachineParams::to_string() const {
    internal_assert(parallelism.type().is_int() &&
      last_level_cache_size.type().is_int() &&
      balance.type().is_int());
    std::ostringstream o;
    o << parallelism << "," << last_level_cache_size << "," << balance;
    return o.str();
  }

  MachineParams::MachineParams(const std::string &s) {
    std::vector<std::string> v = Internal::split_string(s, ",");
    user_assert(v.size() == 3) << "Unable to parse MachineParams: " << s;
    parallelism = Internal::string_to_int(v[0]);
    last_level_cache_size = Internal::string_to_int(v[1]);
    balance = Internal::string_to_int(v[2]);
  }

  }  // namespace Halide











