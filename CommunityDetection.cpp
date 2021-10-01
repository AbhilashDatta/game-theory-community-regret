/*Abhilash Datta*/
#include<bits/stdc++.h>
#include<omp.h>

#define all(x)      x.begin(),x.end()
#define trav(x)     for(auto& i:x)
#define ll          long long
#define endl        '\n'
#define sp          <<" "<<
#define INF         0x3f3f3f3f
#define sum(a)      accumulate(a,a+n,0)
#define forn(i,n)   for(ll i=0;i<n;i++)   //iterate n times with iterator i (variable)
using namespace std;
  
template<typename T> inline void rsort(T& v){ sort(all(v),greater<ll>()); }

template<typename T> void print(T& v, string end = "\n"){
    trav(v) cout<<i<<" ";
    cout<<end;
} 

inline ll count_setbits(ll n){ return __builtin_popcountll(n); }

inline ll count_trailing_zeros(ll n){ return __builtin_ctzll(n); }

string lltos(ll n){
    stringstream sstr;
    sstr<<n;
    return sstr.str();
}



class Graph{

public:    
    map<ll,set<ll>> data;
    vector<vector<ll>> A;

    ll number_of_nodes(){
        return data.size();
    }

    ll number_of_edges(){
        ll edges = 0;
        for(auto i : data){
            edges += i.second.size();
        }
        return edges/2;
    } 

    void scan(fstream& fin){
        string line;
        ll src, dest, ts;
        char comma;
        map<ll,vector<ll>> temp;

        while(fin.peek()!=EOF){
            getline(fin, line);
            stringstream ss(line); 
            ss>>src; ss>>comma; ss>>dest;
            temp[src].push_back(dest); 
            temp[dest].push_back(src); 
        }

        map<ll,ll> label;        
        ll idx = 0;
        set<ll> nodes;

        for(auto i:temp){
            nodes.insert(i.first);
        }

        for(auto i:nodes){
            label[i] = idx;
            idx++;
        }

        for(auto i :temp){
            ll node = i.first;
            for(auto j:i.second){
                this->data[label[node]].insert(label[j]) ;
            }
        }
        ll n = nodes.size();
    
        vector<vector<ll>> t(n,vector<ll>(n,0));

        for(auto i :data){
            ll node = i.first;
            for(auto j:i.second){
                t[node][j] = 1;
                t[j][node] = 1;
            }
        }
        this->A = t;

    } 

    ll degree(ll node_i){
        return data[node_i].size();
    }

    vector<vector<ll>> to_array(){
        return this->A;
    }

    set<ll> neighbors(ll node){
        return this->data[node];
    }
};


double utility(Graph G, ll node_i, vector<ll> S){
    double total_utility = 0;
    ll k_i = G.degree(node_i);
    ll m = G.number_of_edges();
    vector<vector<ll>> A = G.to_array();
    
    for(ll node_j:S){
        if(node_i!=node_j){
            int curr_edges = A[node_i][node_j];
            // cout<<curr_edges<<endl;
            ll k_j = G.degree(node_j);
            // cout<<k_j<<endl;
            
            double degree_prod = (k_i*k_j)/(2.0*m);
            
            double indiv_utility = curr_edges - degree_prod;
            // cout<<indiv_utility<<endl;
            total_utility += indiv_utility;
        }
    }
    return total_utility;
}

double internalCommunityEdges(Graph G, vector<ll> S, vector<ll> node_list, ll community_label){
    double internal_edges = 0;
    for(ll node:node_list){
        for(ll n:G.neighbors(node)){
            if(S[n]== community_label) internal_edges += 1;
        }
    }
    return internal_edges/(2.0);
}

double community_ext(Graph G, vector<ll> S, vector<ll> node_list){
    set<ll> unique_external_nodes;
    ll total_sum = 0;
    ll community_label = S[node_list[0]];
    ll total_connections = 0;
    ll total_ext_node_degree = 0;

    for(ll node:node_list){
        for(ll n : G.neighbors(node)){
            if(S[n]!=S[node]){
                total_connections++;
                unique_external_nodes.insert(n);
            }
        }
    }

    ll communityDegree = unique_external_nodes.size();

    for(ll ext_node: unique_external_nodes){
        total_ext_node_degree += G.degree(ext_node);
    }

    ll totalCommunityEdges = G.number_of_edges() - internalCommunityEdges(G, S,node_list, community_label);
    double modularityComm = total_connections - ((total_ext_node_degree*communityDegree)/(2.0 * totalCommunityEdges));
    modularityComm = modularityComm/(2.0 * totalCommunityEdges);
    return modularityComm;
}

vector<ll> join(Graph G, vector<ll>& S, ll node_i, double lambda, vector<double> probabilities){
    vector<double> max_utility;
    vector<ll> community_to_join;
    
    ll current_community = S[node_i];
    vector<ll> currentCommunity_nodes_list;
    for(ll n:S){
        if(n==current_community){
            currentCommunity_nodes_list.push_back(n);
        }
    }

    double loss = utility(G, node_i, currentCommunity_nodes_list);

    for(ll neighbor:G.neighbors(node_i)){
        ll community_label = S[neighbor];
        community_to_join.push_back(community_label);
        vector<ll> nodes_list;
        for(ll n:S){
            if(n==community_label){
                nodes_list.push_back(n);
            }
        }
        double gain = utility(G,node_i, nodes_list);
        community_label = S[neighbor];

        vector<ll> same_community_nodes_list;
        for(ll n:S){
            if(n==community_label){
                same_community_nodes_list.push_back(n);
            }
        }

        double other = community_ext(G,S,same_community_nodes_list);
        double val = lambda*(gain-loss) + (1-lambda)*other;
        max_utility.push_back(val);
    }

    double maximum_utility_val = *max_element(max_utility.begin(), max_utility.end());
    if(maximum_utility_val>0){
        probabilities[node_i] *= (1-lambda);
    }

    ll maximum_utility_index = max_element(max_utility.begin(), max_utility.end()) - max_utility.begin();
    ll communityIndex = community_to_join[maximum_utility_index];

    S[node_i] = communityIndex;
    return S;
}    

double partitionModularity(Graph G,vector<ll> mod_list){
    double totalModularity = 0;
    for(ll node_i=0; node_i<G.number_of_nodes(); node_i++){
        vector<ll> node_list;
        for(ll n:mod_list){
            if(n==mod_list[node_i]){
                node_list.push_back(n);
            }
        }
        totalModularity += utility(G,node_i,node_list);
    }

    return totalModularity/(2.0*G.number_of_edges());
}

vector<ll> communityDetect(Graph G, vector<ll>& S, ll nIter, double lambda, vector<double> probs){
    vector<double> val;
    srand(time(0));
    for(ll i=0;i<nIter;i++){
        double sum = 0;
        for(auto& i:probs){
            sum += i;
        }

        for(auto& i:probs) i/=sum;

        ll rnode = rand()%G.number_of_nodes();

        cout<<"Iteration "<<i sp rnode<<endl;
        S = join(G,S,rnode, lambda, probs);
        // cout<<(partitionModularity(G,S))<<endl;
    }
    return S;
}


int main(){
    fstream f;
    Graph g;
    f.open("fb-pages-food.txt", ios::in);
    
    g.scan(f);
    vector<ll> S;
    vector<double> probs;

    for(ll i=0;i<g.number_of_nodes();i++){
        S.push_back(i);
        probs.push_back(1.0/g.number_of_nodes());
    }
    
    vector<ll> s = communityDetect(g,S,500,0.8,probs);
    cout<< partitionModularity(g,s) << endl;
    return 0;
}