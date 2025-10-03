#include <iostream>
#include <vector>
#include <queue>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <cmath>
#include <limits>
#include <memory>
#include <functional>

using namespace std;

const double INF = numeric_limits<double>::infinity();
const double EPS = 1e-9;

// Estructura para representar una arista
struct Edge {
    int to;
    double weight;
    Edge(int t, double w) : to(t), weight(w) {}
};

// Clase para el grafo dirigido
class Graph {
public:
    int n;
    vector<vector<Edge>> adj;

    Graph(int vertices) : n(vertices), adj(vertices) {}

    void add_edge(int u, int v, double weight) {
        adj[u].push_back(Edge(v, weight));
    }
};

// Estructura de datos simplificada para Lemma 3.3
class BlockLinkedList {
private:
    int M;
    double B;
    map<int, double> data;  // Simplificado: mapa de clave -> valor

public:
    BlockLinkedList(int M_, double B_) : M(M_), B(B_) {}

    void insert(int key, double value) {
        if (data.find(key) == data.end() || value < data[key]) {
            data[key] = value;
        }
    }

    void batch_prepend(const vector<pair<int, double>>& L) {
        for (const auto& [key, value] : L) {
            if (data.find(key) == data.end() || value < data[key]) {
                data[key] = value;
            }
        }
    }

    pair<vector<int>, double> pull() {
        if (data.empty()) {
            return {{}, B};
        }

        // Ordenar por valor y tomar los M más pequeños
        vector<pair<double, int>> sorted_items;
        for (const auto& [key, value] : data) {
            sorted_items.push_back({value, key});
        }
        sort(sorted_items.begin(), sorted_items.end());

        vector<int> result;
        double x = B;

        int count = min(M, (int)sorted_items.size());
        for (int i = 0; i < count; i++) {
            result.push_back(sorted_items[i].second);
            data.erase(sorted_items[i].second);
        }

        // Actualizar x
        if (!data.empty()) {
            x = data.begin()->second;
        }

        return {result, x};
    }

    bool is_empty() const {
        return data.empty();
    }
};

// Clase principal del algoritmo BMSSP
class BMSSPSolver {
private:
    Graph& graph;
    int n;
    vector<double> db;  // Estimación de distancias
    vector<int> pred;   // Predecesores
    int k;  // log^(1/3)(n)
    int t;  // log^(2/3)(n)

    bool relax_edge(int u, int v, double weight) {
        if (db[u] + weight <= db[v] + EPS) {
            db[v] = db[u] + weight;
            pred[v] = u;
            return true;
        }
        return false;
    }

    // Algorithm 1: FindPivots
    pair<set<int>, set<int>> find_pivots(double B, const set<int>& S) {
        set<int> W = S;
        set<int> W_i_minus_1 = S;

        // Relajar por k pasos
        for (int i = 0; i < k; i++) {
            set<int> W_i;
            for (int u : W_i_minus_1) {
                for (const Edge& e : graph.adj[u]) {
                    if (relax_edge(u, e.to, e.weight)) {
                        if (db[u] + e.weight < B) {
                            W_i.insert(e.to);
                            W.insert(e.to);
                        }
                    }
                }
            }
            W_i_minus_1 = W_i;

            // Si W crece demasiado
            if ((int)W.size() > k * (int)S.size()) {
                return {S, W};
            }
        }

        // Construir bosque F y encontrar raíces grandes
        vector<pair<int, int>> F_edges;
        for (int u : W) {
            for (const Edge& e : graph.adj[u]) {
                if (W.count(e.to) && abs(db[e.to] - (db[u] + e.weight)) < EPS) {
                    F_edges.push_back({u, e.to});
                }
            }
        }

        // DFS para contar tamaños de árboles
        unordered_map<int, int> tree_size;
        unordered_set<int> visited;

        function<int(int)> dfs_count = [&](int u) -> int {
            if (visited.count(u)) return 0;
            visited.insert(u);
            int count = 1;
            for (auto& [fu, fv] : F_edges) {
                if (fu == u) {
                    count += dfs_count(fv);
                }
            }
            return count;
        };

        set<int> P;
        for (int u : S) {
            if (!visited.count(u)) {
                int size = dfs_count(u);
                tree_size[u] = size;
                if (size >= k) {
                    P.insert(u);
                }
            }
        }

        return {P, W};
    }

    // Algorithm 2: BaseCase
    pair<double, set<int>> base_case(double B, const set<int>& S) {
        int x = *S.begin();
        set<int> U0 = {x};

        // Mini Dijkstra
        priority_queue<pair<double, int>, vector<pair<double, int>>, greater<>> heap;
        heap.push({db[x], x});
        set<int> visited;

        while (!heap.empty() && (int)U0.size() < k + 1) {
            auto [dist, u] = heap.top();
            heap.pop();

            if (visited.count(u)) continue;
            visited.insert(u);
            if (u != x) U0.insert(u);

            for (const Edge& e : graph.adj[u]) {
                if (relax_edge(u, e.to, e.weight) && db[u] + e.weight < B) {
                    if (!visited.count(e.to)) {
                        heap.push({db[e.to], e.to});
                    }
                }
            }
        }

        if ((int)U0.size() <= k) {
            return {B, U0};
        } else {
            double B_prime = -INF;
            for (int v : U0) {
                B_prime = max(B_prime, db[v]);
            }
            set<int> U;
            for (int v : U0) {
                if (db[v] < B_prime) {
                    U.insert(v);
                }
            }
            return {B_prime, U};
        }
    }

public:
    BMSSPSolver(Graph& g) : graph(g), n(g.n), db(g.n, INF), pred(g.n, -1) {
        k = max(1, (int)pow(n, 1.0/3.0));
        t = max(1, (int)pow(n, 2.0/3.0));
    }

    // Algorithm 3: BMSSP
    pair<double, set<int>> bmssp(int level, double B, const set<int>& S) {
        // Caso base
        if (level == 0) {
            return base_case(B, S);
        }

        // Encontrar pivotes
        auto [P, W] = find_pivots(B, S);

        // Si P está vacío, retornar inmediatamente
        if (P.empty()) {
            set<int> U;
            for (int v : W) {
                if (db[v] < B) {
                    U.insert(v);
                }
            }
            return {B, U};
        }

        // Inicializar estructura de datos
        int M = max(1, 1 << ((level - 1) * t));
        BlockLinkedList D(M, B);

        for (int x : P) {
            D.insert(x, db[x]);
        }

        int i = 0;
        double B_prime_prev = INF;
        for (int x : P) {
            B_prime_prev = min(B_prime_prev, db[x]);
        }

        set<int> U;
        int threshold = k * (1 << (level * t));

        // Límite de iteraciones para evitar bucle infinito
        int max_iterations = 1000;

        // Iteraciones
        while ((int)U.size() < threshold && !D.is_empty() && i < max_iterations) {
            i++;

            // Pull
            auto [S_i_vec, B_i] = D.pull();
            set<int> S_i(S_i_vec.begin(), S_i_vec.end());

            if (S_i.empty()) break;

            // Llamada recursiva
            auto [B_prime_i, U_i] = bmssp(level - 1, B_i, S_i);
            U.insert(U_i.begin(), U_i.end());

            // Relajar aristas y actualizar D
            vector<pair<int, double>> K;
            for (int u : U_i) {
                for (const Edge& e : graph.adj[u]) {
                    if (relax_edge(u, e.to, e.weight)) {
                        double new_val = db[u] + e.weight;
                        if (B_i <= new_val && new_val < B) {
                            D.insert(e.to, new_val);
                        } else if (B_prime_i <= new_val && new_val < B_i) {
                            K.push_back({e.to, new_val});
                        }
                    }
                }
            }

            // BatchPrepend
            for (int x : S_i) {
                if (B_prime_i <= db[x] && db[x] < B_i) {
                    K.push_back({x, db[x]});
                }
            }
            D.batch_prepend(K);

            // Verificar condición de salida
            if (D.is_empty()) {
                B_prime_prev = B;
                break;
            }

            if ((int)U.size() >= threshold) {
                B_prime_prev = B_prime_i;
                break;
            }
        }

        // Agregar vértices completos de W
        for (int v : W) {
            if (db[v] < B_prime_prev) {
                U.insert(v);
            }
        }

        return {B_prime_prev, U};
    }

    map<int, double> solve_sssp(int source) {
        db[source] = 0.0;

        // Calcular nivel máximo (limitado para grafos pequeños)
        int max_level = 1;
        if (n > 10) {
            max_level = max(1, min(3, (int)ceil(log2(n) / t)));
        }

        // Llamar BMSSP
        auto [B_prime, U] = bmssp(max_level, INF, {source});

        // Retornar distancias
        map<int, double> distances;
        for (int v = 0; v < n; v++) {
            if (db[v] < INF) {
                distances[v] = db[v];
            }
        }

        return distances;
    }

    int get_k() const { return k; }
    int get_t() const { return t; }
};

// Ejemplo de uso
int main() {
    // Crear grafo de ejemplo
    Graph g(6);
    g.add_edge(0, 1, 4.0);
    g.add_edge(0, 2, 2.0);
    g.add_edge(1, 2, 1.0);
    g.add_edge(1, 3, 5.0);
    g.add_edge(2, 3, 8.0);
    g.add_edge(2, 4, 10.0);
    g.add_edge(3, 4, 2.0);
    g.add_edge(3, 5, 6.0);
    g.add_edge(4, 5, 3.0);

    // Resolver SSSP
    BMSSPSolver solver(g);
    auto distances = solver.solve_sssp(0);

    cout << "Distancias mas cortas desde el vertice 0:" << endl;
    for (const auto& [vertex, dist] : distances) {
        cout << "  Vertice " << vertex << ": " << dist << endl;
    }

    cout << "\nParametros del algoritmo:" << endl;
    cout << "  k = " << solver.get_k() << endl;
    cout << "  t = " << solver.get_t() << endl;

    return 0;
}