#include "z3++.h"
#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <queue>
#include <stack>

#include "Global.h"
#include "Stats.h"

using namespace z3;

namespace LazyHorn {

    class neighbor;
    class search_info_node;
    class graph;
    class compare_func_decl;
    class compare_assertions_priority;
    class lazy_horn;

    typedef std::vector<neighbor> neighbors_vec;
    typedef std::vector<neighbors_vec> adjacency_list;
    typedef std::set<func_decl, compare_func_decl> func_decl_set;
    typedef std::vector<func_decl> func_decl_vec;
    typedef std::map<func_decl, int, compare_func_decl> decl_to_int_map;
    typedef std::vector<search_info_node> search_info_vec;
    typedef std::set<int> assertion_set;
    typedef std::vector<expr> lh_expr_vec;
    typedef std::vector<expr_vector> relation_params_vec;
    typedef std::set<int, compare_assertions_priority> edges_queue;

    // class that represents a neighbor of a node in a graph
    class neighbor {
        const int node;
        const int edge;
    public:
        neighbor(int node, int edge) : node(node), edge(edge) {}

        int get_node() const {
            return node;
        }
        int get_edge() const {
            return edge;
        }
    };

    class search_info_node {
        int dist;
        int next_edge;
        int next_node;
    public:
        search_info_node() : dist(INT_MAX), next_edge(-1), next_node(-1) {}

        int get_dist() const {
            return dist;
        }

        void set_dist(int d) {
            assert(d >= 0);
            dist = d;
        }

        int get_next_edge() const {
            return next_edge;
        }

        void set_next_edge(int e) {
            assert(e >= 0);
            next_edge = e;
        }

        int get_next_node() const {
            return next_node;
        }

        void set_next_node(int n) {
            assert(n >= 0);
            next_node = n;
        }
    };

    // class that represents a graph with nodes 0..num_of_nodes and edges 0..num_of_edges
    class graph {
        int num_of_nodes;
        int num_of_edges;
        adjacency_list out_edges;
        adjacency_list in_edges;
        std::unordered_map<int, int> edge_weights;
        std::stack<int> nodes_priority;

        /*
        * finds the shorests path from each node in the graph to dest.
        * info is assumed to be in size num_of_nodes and with init values.
        */
        void dijkstra_shortest_paths_to_dest(int dest, search_info_vec& info) {
            assert(dest < num_of_nodes);
            std::vector<bool> visited(num_of_nodes, false);

            info[dest].set_dist(0);
            int curr_node = dest;

            while (curr_node >= 0) {
                visited[curr_node] = true;

                // try to improved the shortest path to all of the neighbors of curr_node
                for (const neighbor& n : in_edges[curr_node]) {
                    int alt_dist = info[curr_node].get_dist() + edge_weights[n.get_edge()];
                    int n_id = n.get_node();
                    if (alt_dist < info[n_id].get_dist()) {
                        info[n_id].set_dist(alt_dist);
                        info[n_id].set_next_edge(n.get_edge());
                        info[n_id].set_next_node(curr_node);
                    }
                }

                // find next curr_node
                curr_node = -1;
                int min_dist = INT_MAX;
                int i = 0;
                for (const search_info_node& info_node : info) {
                    if ((!visited[i]) && (info_node.get_dist() < min_dist)) {
                        curr_node = i;
                        min_dist = info_node.get_dist();
                    }
                    i++;
                }
            }
        }

        void strong_connect(std::set<int>& vertices, int root, std::stack<int>& edges_stack, int curr_node, int& curr_index, std::stack<int>& vertices_stack, std::map<int, int>& index, std::map<int, int>& lowlink, std::map<int, bool>& on_stack) {
            index[curr_node] = curr_index;
            lowlink[curr_node] = curr_index;
            curr_index += 1;
            vertices_stack.push(curr_node);
            on_stack[curr_node] = true;

            for (const neighbor& n : out_edges[curr_node]) {
                int next_node = n.get_node();
                int next_edge = n.get_edge();
                if ((next_node != root) && (vertices.count(next_node) != 0)) {
                    if (index[next_node] == -1) {
                        strong_connect(vertices, root, edges_stack, next_node, curr_index, vertices_stack, index, lowlink, on_stack);
                        if (lowlink[next_node] < lowlink[curr_node]) {
                            lowlink[curr_node] = lowlink[next_node];
                        }
                        if (!on_stack[next_node]) {
                            edges_stack.push(next_edge);
                        }
                    }
                    else if (on_stack[next_node]) {
                        if (index[next_node] < lowlink[curr_node]) {
                            lowlink[curr_node] = index[next_node];
                        }
                    }
                    else {
                        edges_stack.push(next_edge);
                    }
                }
            }
            for (const neighbor& n : out_edges[curr_node]) {
                if (n.get_node() == root) {
                    edges_stack.push(n.get_edge());
                }
            }

            if (lowlink[curr_node] == index[curr_node]) {
                std::set<int> scc;
                int node = -1;
                do {
                    node = vertices_stack.top();
                    vertices_stack.pop();
                    on_stack[node] = false;
                    scc.insert(node);
                } while (node != curr_node);

                if (curr_node != root) {
                    traversal_order_aux(scc, curr_node, edges_stack);
                }
                else {
                    nodes_priority.push(curr_node);
                }
            }
        }

        void traversal_order_aux(std::set<int>& vertices, int root, std::stack<int>& edges_stack) {
            int curr_index = 0;
            std::stack<int> vertices_stack;
            std::map<int, int> index;
            std::map<int, int> lowlink;
            std::map<int, bool> on_stack;

            for (std::set<int>::iterator it = vertices.begin(); it != vertices.end(); ++it) {
                index[*it] = -1;
                lowlink[*it] = -1;
                on_stack[*it] = false;
            }

            strong_connect(vertices, root, edges_stack, root, curr_index, vertices_stack, index, lowlink, on_stack);
        }
                
        int last_edge(int node, int edge, search_info_vec& info) {
            int curr_node = node;
            int curr_edge = edge;
            while (info[curr_node].get_dist() != 0) {
                curr_edge = info[curr_node].get_next_edge();
                curr_node = info[curr_node].get_next_node();
            }
            return curr_edge;
        }

    public:
        graph() : num_of_nodes(0), num_of_edges(0) {}

        void add_nodes(unsigned int n_nodes) {
            num_of_nodes += n_nodes;
            out_edges.resize(out_edges.size() + n_nodes);
            in_edges.resize(in_edges.size() + n_nodes);
        }

        int get_num_of_nodes() const {
            return num_of_nodes;
        }

        // add an edge to the graph. the default weight of the the edge is 1
        void add_edge(int src, int dest, int edge) {
            assert((src < num_of_nodes) && (dest < num_of_nodes));
            num_of_edges++;
            edge_weights[edge] = 1;
            out_edges[src].push_back(neighbor(dest, edge));
            in_edges[dest].push_back(neighbor(src, edge));
        }

        int get_num_of_edges() const {
            return num_of_edges;
        }

        void set_edge_weight(int edge, int weight) {
            assert(edge_weights.count(edge) != 0);
            edge_weights[edge] = weight;
        }

        int get_edge_weight(int edge) {
            assert(edge_weights.count(edge) != 0);
            return edge_weights[edge];
        }

        neighbors_vec get_neighbors_of_node(int node) const {
            assert(node < num_of_nodes);
            return out_edges[node];
        }

        // returns a vector of the edges on a shortest path from src to dest
        std::vector<int> shortest_path(int src, int dest) {
            assert((src < num_of_nodes) && (dest < num_of_nodes));
            search_info_vec info(num_of_nodes);
            dijkstra_shortest_paths_to_dest(dest, info);

            std::vector<int> path;
            if (info[src].get_dist() < INT_MAX) {
                int next_node = src;
                while (next_node != dest) {
                    path.push_back(info[next_node].get_next_edge());
                    next_node = info[next_node].get_next_node();
                }
            }
            return path;
        }

        /*
        * returns a vector of the edges on a second shortest path from src to dest.
        * the returned vector contains only the edges on the path with weight 1.
        */
        std::vector<int> second_shortest_path(int src, int dest, std::set<int>& back_edges_set) {
            assert((src < num_of_nodes) && (dest < num_of_nodes));
            search_info_vec info(num_of_nodes);
            dijkstra_shortest_paths_to_dest(dest, info);

            std::vector<int> added_assertions;
 
            int begin_node = -1;
            int begin_edge = -1;
            int next_path_weight = INT_MAX;
            
            // if clause_addition_strat is no loops first
            if (gParams.clause_addition_strat == 1) {
                for (int node = 0; node < num_of_nodes; node++) {
                    if (info[node].get_dist() == 0) { // for every already used node
                        for (const neighbor& neighbor : out_edges[node]) {
                            if (edge_weights[neighbor.get_edge()] != 0) { // for every unused outgoing edge
                                if (back_edges_set.count(last_edge(neighbor.get_node(), neighbor.get_edge(), info)) == 0) { // for every node that is not on a loop in the shortest paths tree
                                    int alt_dist = info[neighbor.get_node()].get_dist();
                                    if (alt_dist < next_path_weight) { // check if the new path is shorter than the current path
                                        begin_node = neighbor.get_node();
                                        begin_edge = neighbor.get_edge();
                                        next_path_weight = alt_dist;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            // find the second shortest path
            if (next_path_weight == INT_MAX) {
                for (int node = 0; node < num_of_nodes; node++) {
                    if (info[node].get_dist() == 0) { // for every already used node
                        for (const neighbor& neighbor : out_edges[node]) {
                            if (edge_weights[neighbor.get_edge()] != 0) { // for every unused outgoing edge
                                int alt_dist = info[neighbor.get_node()].get_dist();
                                if (alt_dist < next_path_weight) { // check if the new path is shorter than the current path
                                    begin_node = neighbor.get_node();
                                    begin_edge = neighbor.get_edge();
                                    next_path_weight = alt_dist;
                                }
                            }
                        }
                    }
                }
            }

            // create added_assertions vector
            if (next_path_weight < INT_MAX) {
                added_assertions.push_back(begin_edge);
                int next_node = begin_node;
                while (info[next_node].get_dist() != 0) {
                    int next_edge = info[next_node].get_next_edge();
                    added_assertions.push_back(next_edge);
                    next_node = info[next_node].get_next_node();
                }
            }

            return added_assertions;
        }

        /*
        * returns a vector of the edges of a shortest path from the top most node in nodes_priority 
        * (that has outgoing edges with weight 1) to dest.
        * the returned vector contains only the edges on the path with weight 1.
        */
        std::vector<int> top_down_second_shortest_path(int dest) {
            assert(dest < num_of_nodes);
            search_info_vec info(num_of_nodes);
            dijkstra_shortest_paths_to_dest(dest, info);

            std::vector<int> added_assertions;

            int begin_node = -1;
            int begin_edge = -1;
            int second_shortest_weight = INT_MAX;

            for (const neighbor& neighbor : out_edges[nodes_priority.top()]) {
                if (edge_weights[neighbor.get_edge()] != 0) { // for every unused outgoing edge
                    int alt_dist = info[neighbor.get_node()].get_dist();
                    if (alt_dist < second_shortest_weight) { // check if the new path is shorter than the current path
                        begin_node = neighbor.get_node();
                        begin_edge = neighbor.get_edge();
                        second_shortest_weight = alt_dist;
                    }
                }
            }

            while (begin_node == -1) { // the top node of nodes_priority has no outgoing edges with weight 1
                nodes_priority.pop();
                for (const neighbor& neighbor : out_edges[nodes_priority.top()]) {
                    if (edge_weights[neighbor.get_edge()] != 0) { // for every unused outgoing edge
                        int alt_dist = info[neighbor.get_node()].get_dist();
                        if (alt_dist < second_shortest_weight) { // check if the new path is shorter than the current path
                            begin_node = neighbor.get_node();
                            begin_edge = neighbor.get_edge();
                            second_shortest_weight = alt_dist;
                        }
                    }
                }
            }

            added_assertions.push_back(begin_edge);
            int next_node = begin_node;
            while (info[next_node].get_dist() != 0) {
                int next_edge = info[next_node].get_next_edge();
                added_assertions.push_back(next_edge);
                next_node = info[next_node].get_next_node();
            }

            return added_assertions;
        }

        void traversal_order(int root, std::vector<int>& edges_priority) {
            edges_priority.clear();
            edges_priority.insert(edges_priority.begin(), num_of_edges, -1);
            while (!nodes_priority.empty()) {
                nodes_priority.pop();
            }

            std::set<int> vertices;
            for (int i = 0; i < num_of_nodes; i++) {
                vertices.insert(i);
            }
            std::stack<int> edges_stack;
            
            traversal_order_aux(vertices, root, edges_stack);

            int priority = 0;
            while (!edges_stack.empty()) {
                edges_priority[edges_stack.top()] = priority;
                edges_stack.pop();
                priority++;
            }
        }
        
        void dfs_visit(int node, std::set<int>& back_edges_set, std::set<int>& discovered, std::set<int>& finished) {
            discovered.insert(node);
            
            for (const neighbor& neighbor : out_edges[node]) {
                int next_node = neighbor.get_node();
                if (finished.count(next_node) == 0) {
                    if (discovered.count(next_node) != 0) {
                        back_edges_set.insert(neighbor.get_edge());
                    }
                    else {
                        dfs_visit(next_node, back_edges_set, discovered, finished);
                    }
                }
            }
            
            discovered.erase(node);
            finished.insert(node);
        }
        
        void compute_back_edges(int root, std::set<int>& back_edges_set) {
            std::set<int> discovered;
            std::set<int> finished;
            dfs_visit(root, back_edges_set, discovered, finished);
        }

        std::stack<int> get_nodes_priority() {
            return nodes_priority;
        }

        friend std::ostream& operator<<(std::ostream& out, graph& g);
    };
    inline std::ostream& operator<<(std::ostream& out, graph& g) {
        out << "=================================================================\n";
        out << "my graph has " << g.num_of_nodes << " nodes and " << g.num_of_edges << " edges.\n\n";
        out << "the neighbors of each node:\n";
        for (int i = 0; i < g.num_of_nodes; i++) {
            out << "- node " << i << ":\n";
            for (const neighbor& n : g.out_edges[i]) {
                out << "\t--[" << n.get_edge() << "]--> " << n.get_node() << "\n";
            }
        }
        out << "=================================================================\n";
        return out;
    }

    params init_params(context& c, unsigned int timeout = 0) {
        // set_param("verbose", 10);
        params params(c);
        params.set("engine", "spacer");
        params.set("fp.xform.slice", false);
        params.set("fp.xform.inline_linear", false);
        params.set("fp.xform.inline_eager", false);
        if (timeout > 0) {
            params.set("timeout", timeout);
        }
        params.set("fp.spacer.random_seed", gParams.random_seed);
        // params.set("print_statistics", true);
        
        // arrays
        if (gParams.array_theory == 1) {
            params.set("fp.spacer.ground_pobs", false);
            params.set("fp.spacer.q3.use_qgen", true);
        }
        return params;
    }

    class compare_func_decl {
    public:
        bool operator() (const func_decl& lhs, const func_decl& rhs) const {
            return lhs.id() < rhs.id();
        }
    };

    class compare_assertions_priority {
        std::vector<int>& assertions_priority;
    public:
        compare_assertions_priority(std::vector<int>& a_p) : assertions_priority(a_p) {}
        bool operator() (const int& lhs, const int& rhs) const {
            return assertions_priority[lhs] < assertions_priority[rhs];
        }
    };

    class lazy_horn {
        /*
        * verbosity:
        *   - 0 - no output
        *   - 1 - output the full graph and the final covers (if the problem is unsat)
        *   - 2 - also, output the intermidiate graphs and covers
        *   - 3 - also, output the covers after the addition of new assertions
        */
        int verbosity;

        // timeout in milliseconds. if the value is 0 than there is no timeout.
        unsigned int timeout;
        
        std::string filename;

        context c;
        expr_vector assertions;
        lh_expr_vec covers;

        func_decl_set rel_set;
        func_decl_vec head_rel_vec;
        func_decl_vec body_rel_vec;

        lh_expr_vec body_rel_expr_vec;
        relation_params_vec head_rel_params_vec;
        relation_params_vec body_rel_params_vec;

        decl_to_int_map decl_to_node;
        func_decl_vec node_to_decl; // used for printing the graph
        int root_decl_id;
        int error_decl_id;

        graph rel_graph;

        func_decl_set used_rel_set;
        assertion_set used_assertions_set;
        
        assertion_set back_assertions_set;

        const func_decl root_decl = function("lazy_horn_root_relation", c.bool_sort(), c.bool_sort());
        expr error = c.bool_const("lazy_horn_error_relation");

        int num_of_iters;
        int last_significant_iter;

        std::vector<int> assertions_priority;

        bool is_root_decl(const func_decl& decl) {
            return (decl_to_node[decl] == root_decl_id);
        }

        bool is_error_decl(const func_decl& decl) {
            return (decl_to_node[decl] == error_decl_id);
        }

        /*
        returns the declaration of the head relation of this implies expression.
        if the expression is a query the function returns a func_decl that represents the error node.
        */
        expr get_head_relation(expr const& e) {
            assert(e.is_implies());
            return e.arg(1);
        }

        bool get_body_relation_aux(expr const& e, expr& body_rel_e) {
            assert(e.is_app());

            // check if the current application expression is the relation
            if (rel_set.count(e.decl()) != 0) {
                body_rel_e = e;
                return true;
            }

            // iterate recursively on the children
            for (int i = 0; i < e.num_args(); i++) {
                expr curr = e.arg(i);
                if (curr.is_app()) {
                    if (get_body_relation_aux(curr, body_rel_e)) {
                        return true;
                    }
                }
            }

            return false;
        }

        /*
        returns the declaration of the body relation of this implies expression.
        if the expression is a fact the function returns the expression "true".
        */
        expr get_body_relation(expr const& e) {
            assert(e.is_implies());
            expr body_rel_expr = c.bool_val(true);
            get_body_relation_aux(e.arg(0), body_rel_expr);
            return body_rel_expr;
        }

        /*
        * finds the initial underapproximation which is the shortest path between root and error
        * the function updates used_rel_set, used_assertions_set and the weights of the edges on the path to 0
        */
        void init_underapproximation() {
            LH_MEASURE_FN;
            std::vector<int> under_app = rel_graph.shortest_path(root_decl_id, error_decl_id);

            // initialize used_rel_set with all the nodes on the path and update the weights of the edges
            used_rel_set.insert(root_decl);
            for (int assertion : under_app) {
                used_rel_set.insert(head_rel_vec[assertion]);
                used_assertions_set.insert(assertion);
                rel_graph.set_edge_weight(assertion, 0);
            }
        }

        /*
        * finds the next underapproximation which is the second shortest path between root and error
        * the function updates used_rel_set, used_assertions_set and the weights of the edges on the path to 0
        */
        std::vector<int> next_underapproximation() {
            LH_MEASURE_FN;
            std::vector<int> under_app;
            if (gParams.clause_addition_strat == 2) {
                under_app = rel_graph.top_down_second_shortest_path(error_decl_id);
            }
            else {
                under_app = rel_graph.second_shortest_path(root_decl_id, error_decl_id, back_assertions_set);
            }

            // initialize used_rel_set with all the nodes on the path and update the weights of the edges
            for (int assertion : under_app) {
                used_rel_set.insert(head_rel_vec[assertion]);
                used_assertions_set.insert(assertion);
                rel_graph.set_edge_weight(assertion, 0);
            }

            return under_app;
        }
        
        /*
        * initialize the next fixedpoint solver with the current relations, assertions and covers.
        * call after init_underapproximation and next_underapproximation.
        * use the same context object in every call.
        */
        void set_fixedpoint_same(fixedpoint& fp) {
            // setting the parameters
            fp.set(init_params(c));

            // registering the relations and updating their covers
            for (func_decl decl : used_rel_set) {
                if (!is_root_decl(decl)) {
                    fp.register_relation(decl);
                }
            }

            // adding the rules
            for (int assertion_id : used_assertions_set) {
                symbol name = c.str_symbol(("rule" + std::to_string(assertion_id)).c_str());
                expr rule = assertions[assertion_id];
                if (is_error_decl(head_rel_vec[assertion_id])) {
                    rule = implies(rule.body().arg(0), error);
                }
                fp.add_rule(rule, name);
            }
            
            // injecting the interpretation
            for (func_decl decl : used_rel_set) {
                if (!is_root_decl(decl) && !covers[decl_to_node[decl]].is_true()) {
                    fp.add_cover(-1, decl, covers[decl_to_node[decl]]);
                }
            }
        }

        /*
        * initialize the next fixedpoint solver with the current relations, assertions and covers.
        * call after init_underapproximation and next_underapproximation.
        * use a fresh context object in every call.
        */
        void set_fixedpoint_fresh(fixedpoint& fp1, context& c1, func_decl_set& curr_rel_set) {
            // setting the parameters
            fp1.set(init_params(c1));
            fp1.from_file(filename.data()); // reading the assertions from file
            expr_vector assertions1 = fp1.assertions();
            int i = 0;
            for (expr_vector::iterator it = assertions1.begin(); it != assertions1.end(); ++it, ++i) {
                if (used_assertions_set.count(i) != 0) {
                    expr rule = *it;
                    symbol name = c1.str_symbol(("rule" + std::to_string(i)).c_str());
                    expr head_rel = rule.body().arg(1);
                    if (head_rel.is_false()) {
                        expr error1 = c1.bool_const("lazy_horn_error_relation");
                        func_decl error_decl = error1.decl();
                        curr_rel_set.insert(error_decl);
                        fp1.register_relation(error_decl);
                        expr new_rule = implies(rule.body().arg(0), error1);
                        fp1.add_rule(new_rule, name);
                    }
                    else {
                        func_decl head_rel_decl = head_rel.decl();
                        curr_rel_set.insert(head_rel_decl);
                        fp1.register_relation(head_rel_decl);                        
                        fp1.add_rule(rule, name);
                    }
                }
            }
            
            // injecting the interpretation
            for (func_decl curr_decl : curr_rel_set) {
                for (func_decl decl : used_rel_set) {
                    if (decl.name().str() == curr_decl.name().str()) {
                        expr cover = covers[decl_to_node[decl]];
                        if (!(cover.is_true())) {
                            expr curr_cover = to_expr(c1, Z3_translate(c, cover, c1));
                            fp1.add_cover(-1, curr_decl, curr_cover);
                        }
                    }
                }
            }
        }

        /*
        * update the covers of the relations after the addition of a path to the graph.
        * the graph is traversed according to the priorities of the assertions from the last node in the added path.
        */
        void update_covers(std::vector<int>& path) {
            LH_MEASURE_FN;
            assert(path.size() > 0);

            compare_assertions_priority cmp(assertions_priority);
            edges_queue queue(cmp);

            if (path.size() > 1) {
                update_path(path, queue);
                // is_valid(path, covers[decl_to_node[head_rel_vec[path.back()]]]); // this call was added to update the covers of the intermediate nodes
            }
            else {
                queue.insert(path[0]);
            }
            
            // This loop was added for cases in which spacer returns an incomplete model.
            // This can happen if the problem is solved only by performing simplifications 
            // made by the frontend.
            for (func_decl decl : used_rel_set) {
                if (!is_root_decl(decl) && covers[decl_to_node[decl]].is_true()) {
                    for (const neighbor& n : rel_graph.get_neighbors_of_node(decl_to_node[decl])) {
                        if (!covers[n.get_node()].is_true()) {
                            queue.insert(n.get_edge());
                        }
                    }
                }     
            }

            while (!queue.empty()) {
                
                std::vector<int> edge_path;
                edge_path.push_back(*(queue.begin()));
                queue.erase(queue.begin());
                update_path(edge_path, queue);
                /*
                int edge = *(queue.begin());
                queue.erase(queue.begin());
                update_edge(edge, queue);*/
            }
        }

        void update_path(std::vector<int>& path, edges_queue& queue) {
            LH_MEASURE_FN;
            assert(path.size() > 0);

            bool change = false;
            int last_node = decl_to_node[head_rel_vec[path.back()]];

            expr curr_cover = covers[last_node];
            if (curr_cover.is_true()) {
                return;
            }

            expr_vector new_cover_conjs(c);

            // iterate over the conjunctions of the current cover
            if (curr_cover.is_and()) {
                if (path.size() > 1) {
                    for (int i = 0; i < curr_cover.num_args(); i++) {
                        expr conj = curr_cover.arg(i);
                        new_cover_conjs.push_back(conj);
                        if (!is_valid(path, mk_and(new_cover_conjs))) {
                            new_cover_conjs.pop_back();
                            change = true;
                        }
                    }
                } else {
                    for (int i = 0; i < curr_cover.num_args(); i++) {
                        expr conj = curr_cover.arg(i);
                        if (is_valid(path, conj)) {
                            new_cover_conjs.push_back(conj);
                        } 
                        else {
                            change = true;
                        }
                    }
                }
            }
            else {
                if (is_valid(path, curr_cover)) {
                    new_cover_conjs.push_back(curr_cover);
                }
                else {
                    change = true;
                }
            }

            if (change) {
                // update the cover
                int num_of_conjs = new_cover_conjs.size();
                if (num_of_conjs == 0) {
                    covers[last_node] = c.bool_val(true);
                }
                else if (num_of_conjs == 1) {
                    covers[last_node] = new_cover_conjs.back();
                }
                else {
                    covers[last_node] = mk_and(new_cover_conjs);
                }

                // insert the neighbors (with cover other than true) to the queue
                for (const neighbor& n : rel_graph.get_neighbors_of_node(last_node)) {
                    if (!covers[n.get_node()].is_true()) {
                        queue.insert(n.get_edge());
                    }
                }
            }
        }

        void update_covers_bfs(std::vector<int>& path) {
            LH_MEASURE_FN;
            assert(path.size() > 0);

            std::queue<int> queue;

            if (path.size() > 1) {
                update_path(path, queue);
            }
            else {
                queue.push(path[0]);
            }
            
            // This loop was added for cases in which spacer returns an incomplete model.
            // This can happen if the problem is solved only by performing simplifications 
            // made by the frontend.
            for (func_decl decl : used_rel_set) {
                if (!is_root_decl(decl) && covers[decl_to_node[decl]].is_true()) {
                    for (const neighbor& n : rel_graph.get_neighbors_of_node(decl_to_node[decl])) {
                        if (!covers[n.get_node()].is_true()) {
                            queue.push(n.get_edge());
                        }
                    }
                }     
            }

            while (!queue.empty()) {
                std::vector<int> edge_path;
                edge_path.push_back(queue.front());
                queue.pop();
                update_path(edge_path, queue);
            }
        }

        void update_path(std::vector<int>& path, std::queue<int>& queue) {
            LH_MEASURE_FN;
            assert(path.size() > 0);

            bool change = false;
            int last_node = decl_to_node[head_rel_vec[path.back()]];

            expr curr_cover = covers[last_node];
            if (curr_cover.is_true()) {
                return;
            }

            expr_vector new_cover_conjs(c);

            // iterate over the conjunctions of the current cover
            if (curr_cover.is_and()) {
                if (path.size() > 1) {
                    for (int i = 0; i < curr_cover.num_args(); i++) {
                        expr conj = curr_cover.arg(i);
                        new_cover_conjs.push_back(conj);
                        if (!is_valid(path, mk_and(new_cover_conjs))) {
                            new_cover_conjs.pop_back();
                            change = true;
                        }
                    }
                } else {
                    for (int i = 0; i < curr_cover.num_args(); i++) {
                        expr conj = curr_cover.arg(i);
                        if (is_valid(path, conj)) {
                            new_cover_conjs.push_back(conj);
                        } 
                        else {
                            change = true;
                        }
                    }
                }
            }
            else {
                if (is_valid(path, curr_cover)) {
                    new_cover_conjs.push_back(curr_cover);
                }
                else {
                    change = true;
                }
            }

            if (change) {
                // update the cover
                int num_of_conjs = new_cover_conjs.size();
                if (num_of_conjs == 0) {
                    covers[last_node] = c.bool_val(true);
                }
                else if (num_of_conjs == 1) {
                    covers[last_node] = new_cover_conjs.back();
                }
                else {
                    covers[last_node] = mk_and(new_cover_conjs);
                }

                // insert the neighbors (with cover other than true) to the queue
                for (const neighbor& n : rel_graph.get_neighbors_of_node(last_node)) {
                    if (!covers[n.get_node()].is_true()) {
                        queue.push(n.get_edge());
                    }
                }
            }
        }

        bool is_valid(std::vector<int>& path, expr cover) {
            LH_MEASURE_FN;
            assert(path.size() > 0);

            lh_expr_vec path_assertions;
            for (int assertion_id : path) {
                expr assertion = assertions[assertion_id];
                assert(assertion.is_forall());
                path_assertions.push_back(assertion.body());
            }
            
            // replace the body relation of the first assertion with its cover (if it is not the root relation)
            path_assertions[0] = substitute_body(path[0], path_assertions[0], c);

            // replace the head relation of the last assertion with the given cover (if it is not the error relation)
            path_assertions[path_assertions.size() - 1] = substitute_head(path.back(), path_assertions[path_assertions.size() - 1], cover);

            // create the new fixedpoint problem
            
            fixedpoint fp(c);
            fp.set(init_params(c, timeout));
            for (int i = 0; i < path.size(); i++) {
                if (i < path.size() - 1) {
                    func_decl head_rel_decl = head_rel_vec[path[i]];
                    fp.register_relation(head_rel_decl);
                    fp.add_cover(-1, head_rel_decl, covers[decl_to_node[head_rel_decl]]);
                }
                else {
                    func_decl error_decl = error.decl();
                    fp.register_relation(error_decl);
                }
                symbol name = c.str_symbol(("rule" + std::to_string(path[i])).c_str());
                fp.add_rule(path_assertions[i], name);
            }
            
            check_result res = unknown;
            try {
                res = fp.query(error);
            }
            catch (z3::exception& ex) {
                std::cout << "unexpected error: " << ex << "\n";
            }

            if (res == unsat) {
                // updating the covers of the intermediate nodes if is_valid
                for (int i = 0; i < path.size() - 1; i++) {
                    func_decl head_rel_decl = head_rel_vec[path[i]];
                    covers[decl_to_node[head_rel_decl]] = fp.get_cover_delta(-1, head_rel_decl);
                }
                return true;
            }

            return false;
        }

        // replace the body relation of the first assertion with its cover (if it is not the root relation)
        expr substitute_body(int assertion_id, expr assertion, context& c) {
            if (!is_root_decl(body_rel_vec[assertion_id])) {
                expr body_rel = body_rel_expr_vec[assertion_id];
                expr_vector body_rel_params = body_rel_params_vec[assertion_id];

                expr body_rel_cover = covers[decl_to_node[body_rel.decl()]];
                expr body_rel_cover_sub = body_rel_cover.substitute(body_rel_params);
                expr_vector body_rel_singelton(c);
                body_rel_singelton.push_back(body_rel);
                expr_vector body_rel_cover_sub_singleton(c);
                body_rel_cover_sub_singleton.push_back(body_rel_cover_sub);

                return assertion.substitute(body_rel_singelton, body_rel_cover_sub_singleton);
            }
            return assertion;
        }

        // replace the head relation of the last assertion with the given cover (if it is not the error relation)
        expr substitute_head(int assertion_id, expr assertion, expr cover) {
            if (!is_error_decl(head_rel_vec[assertion_id])) {
                expr_vector head_rel_params = head_rel_params_vec[assertion_id];
                expr head_rel_cover_sub = cover.substitute(head_rel_params);
                return implies(assertion.arg(0) && (!head_rel_cover_sub), error);
            }
            return implies(assertion.arg(0), error);
        }

        expr substitute_head_solver(int assertion_id, expr assertion, expr cover) {
            if (!is_error_decl(head_rel_vec[assertion_id])) {
                expr_vector head_rel_params = head_rel_params_vec[assertion_id];
                expr head_rel_cover_sub = cover.substitute(head_rel_params);
                return implies(assertion.arg(0) && !head_rel_cover_sub, c.bool_val(false));
            }
            return implies(assertion.arg(0), c.bool_val(false));
        }
        
    public:
        lazy_horn(char const* file, int verb = 0, unsigned int timeout = 0) : filename(file), verbosity(verb), timeout(timeout), assertions(c), num_of_iters(0), last_significant_iter(0) {
            LH_MEASURE_FN;
            fixedpoint fp(c);
            fp.set(init_params(c)); // setting the solver's parameters
            fp.from_file(file); // reading the assertions from file
            assertions = fp.assertions();

            // creating the set and vector of head relations and the vector of head relations parameters and registering the relations
            rel_set.insert(root_decl);
            for (const expr& rule : assertions) {
                expr head_expr = get_head_relation(rule.body());
                func_decl head_decl = head_expr.decl();
                if (head_expr.is_false()) {
                    head_expr = error;
                    head_decl = error.decl();
                }
                rel_set.insert(head_decl);
                head_rel_vec.push_back(head_decl);

                expr_vector head_rel_params(c);
                for (int i = 0; i < head_expr.num_args(); i++) {
                    head_rel_params.push_back(head_expr.arg(i));
                }
                head_rel_params_vec.push_back(head_rel_params);
            }

            // creating the map between func_decl to int id and initializing the covers vector
            int i = 0;
            for (const func_decl& decl : rel_set) {
                decl_to_node[decl] = i;
                node_to_decl.push_back(decl);
                if (decl.name() == error.decl().name()) {
                    error_decl_id = i;
                }
                else if (decl.name() == root_decl.name()) {
                    root_decl_id = i;
                }
                covers.push_back(c.bool_val(true));
                i++;
            }

            rel_graph.add_nodes(rel_set.size());

            // creating the vector of body relations and the vector of body relations parameters and adding the edges to the relations graph
            i = 0;
            for (const expr& rule : assertions) {
                expr body_expr = get_body_relation(rule.body());
                func_decl body_decl = body_expr.decl();
                if (body_expr.is_true()) {
                    body_decl = root_decl;
                }
                body_rel_vec.push_back(body_decl);
                body_rel_expr_vec.push_back(body_expr);

                expr_vector body_rel_params(c);
                for (int i = 0; i < body_expr.num_args(); i++) {
                    body_rel_params.push_back(body_expr.arg(i));
                }
                body_rel_params_vec.push_back(body_rel_params);

                rel_graph.add_edge(decl_to_node[body_decl], decl_to_node[head_rel_vec[i]], i);
                i++;
            }

            rel_graph.traversal_order(root_decl_id, assertions_priority);
            if (gParams.clause_addition_strat == 1) {
                rel_graph.compute_back_edges(root_decl_id, back_assertions_set);
            }
        }

        expr_vector get_assertions() const {
            return assertions;
        }

        func_decl_set get_relations_set() const {
            return rel_set;
        }

        func_decl_vec get_head_relations_vec() const {
            return head_rel_vec;
        }

        func_decl_vec get_body_relations_vec() const {
            return body_rel_vec;
        }

        graph get_relations_graph() const {
            return rel_graph;
        }

        func_decl_set get_used_relations_set() const {
            return used_rel_set;
        }

        assertion_set get_used_assertions_vec() const {
            return used_assertions_set;
        }

        int get_num_of_iterations() {
            return num_of_iters;
        }

        int get_last_significant_iteration() {
            return last_significant_iter;
        }

        int get_num_of_assertions() {
            return assertions.size();
        }

        int get_num_of_needed_assertions() {
            return used_assertions_set.size();
        }

        std::vector<int> get_assertions_priority() {
            return assertions_priority;
        }

        lh_expr_vec get_covers() {
            return covers;
        }

        func_decl_vec get_node_to_decl() {
            return node_to_decl;
        }

        int get_root_decl_id() {
            return root_decl_id;
        }

        int get_error_decl_id() {
            return error_decl_id;
        }
        
        check_result query_same(fixedpoint& fp) {
            check_result res = unknown;
            set_fixedpoint_same(fp);
            try {
                res = fp.query(error);
            }
            catch (z3::exception& ex) {
                std::cout << "unexpected error: " << ex << "\n";
            }
            
            // update the covers
            for (func_decl decl : used_rel_set) {
                if (!is_root_decl(decl)) {
                    if (res == unsat) {
                        covers[decl_to_node[decl]] = fp.get_cover_delta(-1, decl);
                    }
                    else {
                        covers[decl_to_node[decl]] = c.bool_val(true);
                    }
                }
            }
            
            return res;
        }
        
        check_result query_fresh() {
            context c1;
            fixedpoint fp1(c1);
            func_decl_set curr_rel_set;
            set_fixedpoint_fresh(fp1, c1, curr_rel_set); // initialize the solver
            check_result res = unknown;
            try {
                expr error1 = c1.bool_const("lazy_horn_error_relation");
                res = fp1.query(error1);
            }
            catch (z3::exception& ex) {
                std::cout << "unexpected error: " << ex << "\n";
            }
                
            // update the covers
            for (func_decl curr_decl : curr_rel_set) {
                expr cover = fp1.get_cover_delta(-1, curr_decl);
                for (func_decl decl : used_rel_set) {
                    if (decl.name().str() == curr_decl.name().str()) {
                        if (res == unsat) {
                            expr curr_cover = to_expr(c, Z3_translate(c1, cover, c));
                            covers[decl_to_node[decl]] = curr_cover;
                        }
                        else {
                            covers[decl_to_node[decl]] = c.bool_val(true);
                        }
                    }
                }
            }
            
            return res;
        }

        check_result query() {
            LH_MEASURE_FN;
            init_underapproximation(); // find the initial underapproximation

            int iter = 0;
            if (verbosity > 0) {
                std::cout << "=================================================================\n";
                std::cout << "\t\t        The full problem" << std::endl;
                std::cout << "=================================================================\n";
                print_full_relations_graph();
                std::cout << std::endl;
                if (verbosity > 1) {
                    std::cout << "=================================================================\n";
                    std::cout << "\t\t\t   iteration " << iter << std::endl;
                    std::cout << "=================================================================\n";
                    print_used_relations_graph();
                }
            }
            
            fixedpoint fp(c);
            
            while (true) {
                check_result res = unknown;
                if (gParams.context_strat == 0) {
                    if (iter != 0) {
                        fp = fixedpoint(c);
                    }
                    res = query_same(fp);
                }
                else {
                    res = query_fresh();
                }
                
                last_significant_iter = iter + 1;
                Stats::uset("LSIter", last_significant_iter);
                // the partial problem is unsafe
                if (res == sat) {
                    num_of_iters = iter + 1;
                    return res;
                }

                // the partial problem is safe or unknown

                // print the covers
                if (verbosity > 1 || (verbosity == 1 && used_assertions_set.size() == assertions.size())) {
                    std::cout << std::endl << "The cover of each relation after querying:\n";
                    for (func_decl decl : used_rel_set) {
                        std::string name = decl.name().str();
                        if (is_root_decl(decl)) {
                            name = "root";
                        }
                        else if (is_error_decl(decl)) {
                            name = "error";
                        }
                        std::cout << "- " << name << ":\n\t";
                        std::cout << covers[decl_to_node[decl]] << "\n";
                    }
                }
                
                do {
                    // the full problem is safe
                    if (used_assertions_set.size() == assertions.size()) {
                        num_of_iters = iter + 1;
                        return res;
                    }

                    iter++;
                    std::vector<int> path = next_underapproximation(); // find the next underapproximation

                    if (verbosity > 1) {
                        std::cout << std::endl;
                        std::cout << "=================================================================\n";
                        std::cout << "\t\t\t   iteration " << iter << std::endl;
                        std::cout << "=================================================================\n";
                        print_used_relations_graph();
                    }

                    // update and print the covers
                    if (gParams.cover_update_strat == 0) {
                        update_covers(path);
                    } else if (gParams.cover_update_strat ==1) {
                        update_covers_bfs(path);
                    }

                    if (verbosity > 1 || (verbosity == 1 && used_assertions_set.size() == assertions.size())) {
                        if (verbosity == 1) {
                            std::cout << "The number of iterations: " << iter + 1 << std::endl;
                        }

                        std::cout << std::endl << "The cover of each relation after expanding the underapproximation:\n";
                        for (func_decl decl : used_rel_set) {
                            std::string name = decl.name().str();
                            if (is_root_decl(decl)) {
                                name = "root";
                            }
                            else if (is_error_decl(decl)) {
                                name = "error";
                            }
                            std::cout << "- " << name << ":\n\t";
                            std::cout << covers[decl_to_node[decl]] << "\n";
                        }
                    }
                    Stats::uset("Iters", iter);
                    VERBOSE(1, Stats::PrintBrunch(vout()););
                } while (covers[error_decl_id].is_false());
                
                Stats::uset("Iters", iter);
                VERBOSE(1, Stats::PrintBrunch(vout()););
            }

            return unknown;
        }

        void print_full_relations_graph() {
            std::cout << "The full graph has " << rel_graph.get_num_of_nodes() << " relation nodes and " << rel_graph.get_num_of_edges() << " assertion edges.\n\n";
            std::cout << "The neighbors of each relation:\n";
            for (int i = 0; i < rel_graph.get_num_of_nodes(); i++) {
                std::string name = node_to_decl[i].name().str();
                if (name == "lazy_horn_root_relation") {
                    name = "root";
                }
                else if (name == "lazy_horn_error_relation") {
                    name = "error";
                }
                std::cout << "- " << name << ":\n";
                neighbors_vec neighbors = rel_graph.get_neighbors_of_node(i);
                for (const neighbor& n : neighbors) {
                    name = node_to_decl[n.get_node()].name().str();
                    if (name == "lazy_horn_error_relation") {
                        name = "error";
                    }
                    std::cout << "\t--[" << n.get_edge() << "]--> " << name << "\n";
                }
            }
        }

        void print_used_relations_graph() {
            std::cout << "The current graph has " << used_rel_set.size() << " relation nodes and " << used_assertions_set.size() << " assertion edges.\n\n";
            std::cout << "The neighbors of each relation : \n";
            for (func_decl decl : used_rel_set) {
                std::string name = decl.name().str();
                if (name == "lazy_horn_root_relation") {
                    name = "root";
                }
                else if (name == "lazy_horn_error_relation") {
                    name = "error";
                }
                std::cout << "- " << name << ":\n";
                neighbors_vec neighbors = rel_graph.get_neighbors_of_node(decl_to_node[decl]);
                for (const neighbor& n : neighbors) {
                    if (used_assertions_set.count(n.get_edge()) != 0) {
                        name = node_to_decl[n.get_node()].name().str();
                        if (name == "lazy_horn_error_relation") {
                            name = "error";
                        }
                        std::cout << "\t--[" << n.get_edge() << "]--> " << name << "\n";
                    }
                }
            }
        }
    };
}
