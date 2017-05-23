#include <iostream>
#include <cmath>
#include <string>
#include <cstring>
#include <climits>
#include <sstream>
#include <cstdlib>
#include <deque>
#include <vector>
#include <algorithm>
#include <fstream>
#include <set>
#include <map>
#include <ctime>

using namespace std;

const double INF = 10.0;
const double in_out_cost = 0.000001;

int n, m, k = INF, n_paths;
int n_routers, n_links;
int s = 0, t;
double target;
vector<double> p_router;
vector <double> costs;
double cost = 1.0;
vector < deque<int> > paths;
vector< deque<int> > real_paths;
int cur_paths;
int min_path_len;
bool flag_was_parted = true;
vector <int> in_verts, out_verts;

struct rib {
	int b, u, f, iter;
	double c;
	size_t back;
	rib (int a1, int a2, double a3, int a4, int a5, size_t s1) : b(a1), u(a2), c(a3), f(a4), iter(a5), back(s1) {};
};

vector < vector<rib> > g;
map <int, vector<int> > graph;
map <int, vector<int> > start_graph;

void add_rib (vector < vector<rib> > & g, int a, int b, int u, double c, int iter) {  //a - откуда, b - куда, c - cost

	rib r1(b, u, c, 0, iter, g[b].size() );
	rib r2( a, 0, -c, 0, iter, g[a].size() );
	g[a].push_back (r1);
	g[b].push_back (r2);
}

vector<int> func(int a_i, vector< vector<rib> > g)
{
	for (int i = 0; i < 7; i ++) {
		if (g[a_i][i].f > 0)
			return func(i, g);
	}
}

void paths_to_real_paths()
{
    real_paths.clear();
    real_paths.resize(paths.size());
    for (int i = 0; i < paths.size(); ++i) {
        for (int j = 0; j < paths[i].size(); ++j) {
            if (paths[i][j] == 0 || j % 2) {
                real_paths[i].push_back(paths[i][j]);
            }
        }
    }
}

void to_orient_graph(int NUMOFVERTS, int NUMOFEDGES, pair<int, int> * edges)
{
    double w[NUMOFVERTS][NUMOFVERTS];

    for (int i = 0; i < NUMOFVERTS; i++)
        for (int j = 0; j < NUMOFVERTS; j++)
            w[i][j] = -1.0;

    for (int i = 0; i < NUMOFEDGES; i++) {
        int a, b;
        a = edges[i].first;
        b = edges[i].second;
        w[a][b] = costs[b];
        w[b][a] = costs[a];
    }

    double one_w[2 * NUMOFVERTS - 2][2 * NUMOFVERTS - 2];
    int new_num = 2 * NUMOFVERTS - 2;
    for (int i = 0; i < NUMOFVERTS; i++) {
    	if (i != 0 && i != (NUMOFVERTS - 1)) {

    		for (int j = 1; j < NUMOFVERTS - 1; j++) {
    			if (j != i) {
    				one_w[j + NUMOFVERTS - 1][i] = w[j][i];
    				one_w[NUMOFVERTS - 1 + i][j] = w[i][j];
    				one_w[j][NUMOFVERTS - 1 + i] = -1.0;
    				one_w[i][j] = -1.0;
    			}
    			else {
    				one_w[i][i] = -1.0;
    				one_w[i][NUMOFVERTS + i - 1] = 0.000001;
    				one_w[NUMOFVERTS + i - 1][i] = -1.0;
    			}
    		}
    		//one_w[i + NUMOFVERTS - 1][NUMOFVERTS - 1] = w[i][NUMOFVERTS - 1];
    	} else if (i == 0) {
    		for (int j = 0; j < NUMOFVERTS - 1; j++) {
    			one_w[i][j] = w[i][j];
    			one_w[j][i] = -1.0;
    			if (j != NUMOFVERTS - 1) {
    				one_w[i][NUMOFVERTS - 1 + j] = -1.0;
    				one_w[NUMOFVERTS - 1 + j][i] = -1.0;
    			}
    		}
    	} else if (i == (NUMOFVERTS - 1)) {
    		for (int j = 0; j < NUMOFVERTS - 1; j++) {
    			one_w[i][j] = -1.0;
    			one_w[i][NUMOFVERTS - 1 + j] = -1.0;
    			if (j != i) {
    				one_w[j][i] = -1.0;
    				one_w[NUMOFVERTS - 1 + j][i] = w[j][i];
    			}
    		}
    	}
    }

    for (int i = NUMOFVERTS; i < new_num; i++) {
    	for (int j = NUMOFVERTS; j < new_num; j++) {
    		one_w[i][j] = -1.0;
    	}
    }

    g.resize(2 * NUMOFVERTS - 2);
    costs.resize(2 * NUMOFVERTS - 2);
    int new_m = 0;
    for (int i = 0; i < 2 * NUMOFVERTS - 2; i++) {
    	for (int j = 0; j < 2 * NUMOFVERTS - 2; j++) {
    		if (one_w[i][j] != -1.0) {
                add_rib(g, i, j, 1, one_w[i][j], -1);
                ++new_m;
                costs[j] = one_w[i][j];
    		}
    	}

    }
    m = new_m;
    n = 2 * NUMOFVERTS - 2;

    in_verts.push_back(t);
    for (int i = 1; i < t; ++i) {
        in_verts.push_back(i);
    }
    out_verts.push_back(0);
    for (int i = t+1; i < n; ++i) {
        out_verts.push_back(i);
    }
}

vector < deque<int> > search_path()
{
    int numbFound = 0;

	vector < deque<int> > paths_take;
	vector < double > paths_take_cost;

	int flow = 0;
	cost = 1.0;
	int target_find = n_paths;
	while (target < cost || numbFound < target_find) {
		vector<int> id (n, 0);
		vector<double> global_coef(n, 0);
		global_coef[0] = cost;
		vector<double> d (n, INF);
		vector<int> q (n);
		vector<int> p (n);
		vector<size_t> p_rib (n);
		int globalSwitch =10000;
		deque<int> cur_path;

		int numbOfPartPath;

		int qh=0, qt=0;
		q[qt++] = s;
		d[s] = 0.0;
		while (qh != qt) {
			int v = q[qh++];
			id[v] = 2;
			if (qh == n)
				qh = 0;
			for (size_t i = 0; i < g[v].size(); ++i) {

				rib & r = g[v][i];

				if(r.f < r.u && v !=t) {

					bool flag_rb = false;
					bool flag_v = false;
					int pos_rb = 0;
					int pos_v = 0;

					if (v != 0) {
						for (int i_s = 0; i_s < paths_take.size(); i_s++) {
							for (int j_s = 0; j_s < paths_take[i_s].size(); j_s++) {
								if (v == paths_take[i_s][j_s]) {
									numbOfPartPath = i_s;
									pos_v = j_s;
									flag_v = true;
								}
								if (r.b == paths_take[i_s][j_s]) {
									numbOfPartPath = i_s;
									flag_rb = true;
									pos_rb = j_s;
								}
							}
							if (flag_v && flag_rb)
								break;
						}
					}

					if (flag_rb && flag_v && r.c > 0)
					{
						continue;
					} else if (flag_rb && r.c > 0) {

						double cur_mult = 0.0;
						for (int cur_cost = pos_rb + 1; cur_cost < paths_take[numbOfPartPath].size() - 1; cur_cost++) {
							cur_mult = 1.0 - (1.0 - cur_mult) * (1.0 - costs[paths_take[numbOfPartPath][cur_cost]]);
						}

						cur_mult = 1.0 - (1.0 - d[v]) * (1.0 - r.c) * (1.0 - cur_mult);
						cur_mult += 1.0;

						if (cur_mult < d[r.b]) {
							d[r.b] = cur_mult;
							if (id[r.b] == 0) {
								q[qt++] = r.b;
								if (qt == n)
									qt = 0;
							}
							else if (id[r.b] == 2) {
								if (--qh == -1)
									qh = n-1;
								q[qh] = r.b;
							}

							id[r.b] = 1;
							p[r.b] = v;
							p_rib[r.b] = i;
						}
					} else if (r.c < 0 && r.b != s) {
						if (d[r.b] > d[v]) {

							d[r.b] = d[v];
							if (id[r.b] == 0) {
								q[qt++] = r.b;
								if (qt == n)
									qt = 0;
							}
							else if (id[r.b] == 2) {
								if (--qh == -1)
									qh = n-1;
								q[qh] = r.b;
							}

							id[r.b] = 1;

							p[r.b] = v;
							p_rib[r.b] = i;
						}
					} else if (r.c > 0 && flag_v) {
						double cur_mult = 0.0;
						for (int cur_cost = 1; cur_cost < pos_v + 1; cur_cost++) {
							cur_mult = 1.0 - (1.0 - cur_mult) * (1.0 - costs[paths_take[numbOfPartPath][cur_cost]]);
						}

						cur_mult = 1.0 - (1.0 - cur_mult) * (1.0 - r.c);

						if ((global_coef[r.b] == 0 && cur_mult <= d[r.b]) || (global_coef[r.b] != 0 && cur_mult * (d[v] - 1.0) < d[r.b] * global_coef[r.b] )) {
							d[r.b] = cur_mult;
							if (id[r.b] == 0) {
								q[qt++] = r.b;
								if (qt == n)
									qt = 0;
							}
							else if (id[r.b] == 2) {
								if (--qh == -1)
									qh = n-1;
								q[qh] = r.b;
							}

							id[r.b] = 1;
							p[r.b] = v;
							p_rib[r.b] = i;

							global_coef[r.b] = (d[v] - 1.0) * (cost / paths_take_cost[numbOfPartPath]);
						}

					} else if (d[v] < 1.0) {
 						if ( (global_coef[r.b] == 0 && (1.0 - (1.0 - d[v]) * (1.0 - r.c) ) < d[r.b]) ||
 							((global_coef[r.b] != 0 && global_coef[v] * (1.0 - (1.0 - d[v]) * (1.0 - r.c)) < d[r.b] * global_coef[r.b] ))) {

							d[r.b] = 1.0 - (1.0 - d[v]) * (1.0 - r.c);
							if (id[r.b] == 0) {
								q[qt++] = r.b;
								if (qt == n)
									qt = 0;
							}
							else if (id[r.b] == 2) {
								if (--qh == -1)
									qh = n-1;
								q[qh] = r.b;
							}

							id[r.b] = 1;

							p[r.b] = v;
							p_rib[r.b] = i;
							if (global_coef[v] > 0) {
								global_coef[r.b] = global_coef[v];
							}


						}


					}

				}

			}
		}

		if (d[t] == INF) {
			cout << endl;
			cout << "Not enough probability, probability is only:" << cost << endl;
			if (numbFound < target_find)
				cout << "Not enough paths found, found only: " << numbFound << endl;
			break;
		}

		int addflow = k - flow;

		for (int v=t; v!=s; v=p[v]) {

			int pv = p[v];  size_t pr = p_rib[v];
			addflow = min (addflow, g[pv][pr].u - g[pv][pr].f);
		}

		cur_path.push_back(t);

		double pre_cost = 1;

		bool flag_first = true;
		bool flag_second = true;
		int numbOfSamePath = 10000;
		int vertFirst = 0;
		int vertFirstPos = 0;
		int vertSecond = 0;
		int vertSecondPos = 0;

		deque<int> path_first;
		deque<int> path_second;

		path_first.push_back(t);

		int counter = 0;

		for (int v=t; v!=s; v=p[v]) {
			int pv = p[v];  size_t pr = p_rib[v],  r = g[pv][pr].back;
 			g[pv][pr].f += addflow;
			g[v][r].f -= addflow;

			if(v != t)
				pre_cost *= (1 - 1.0 * g[pv][pr].c / 100) * addflow;


			if (pv != t && pv != s) {
				if (numbOfSamePath == 10000) {
					for (int f_i = 0; f_i < paths_take.size(); f_i++) {
						for (int f_j = 0; f_j < paths_take[f_i].size(); f_j++) {
							if (pv == paths_take[f_i][f_j] && flag_first) {
								numbOfSamePath = f_i;
								vertFirst = pv;
								vertFirstPos = f_j;
								path_first.push_front(pv);
								counter = vertFirstPos;
								flag_first = false;
								break;
							}
						}
						if (!flag_first)
							break;
					}

				} else if(flag_second) {
					for (int f_j = counter + 1; f_j < paths_take[numbOfSamePath].size(); f_j++) {
						if (pv == paths_take[numbOfSamePath][f_j]) {
							vertSecond = pv;
							vertSecondPos = f_j;
							break;
						} else {
							flag_second = false;
							path_second.push_front(pv);
							break;
						}

					}

					counter++;
				} else {
					path_second.push_front(pv);

				}
			}
			if (flag_first)
				path_first.push_front(pv);

			cur_path.push_front(pv);
		}

		if (numbOfSamePath != 10000) {
			for (int f_back = vertSecondPos; f_back < paths_take[numbOfSamePath].size(); f_back++)
				path_second.push_back(paths_take[numbOfSamePath][f_back]);
			path_second.push_front(0);
		}
		//ADD FRONT

		for (int f_front = vertFirstPos - 1; f_front >= 0; f_front--)
			path_first.push_front(paths_take[numbOfSamePath][f_front]);


		if (numbOfSamePath != 10000) {
			paths_take.erase(paths_take.begin() + numbOfSamePath);
			paths_take.push_back(path_first);
			paths_take.push_back(path_second);
		} else {
			paths_take.push_back(cur_path);
		}




		cout << endl;

		cost = 1;
		paths_take_cost.push_back(0);

		for (int i_cost = 0; i_cost < paths_take.size(); i_cost++) {
			double cur_cost = 0;
			cout << "Path " << i_cost + 1 << ": ";
			for (int j_cost = 0; j_cost < paths_take[i_cost].size() - 1; j_cost++) {
				if(flag_was_parted) {
					if (paths_take[i_cost][j_cost] == 0 || j_cost % 2) {
						cout << paths_take[i_cost][j_cost] << " ";
						cur_cost = 1.0 - 1.0 * (1.0 - cur_cost) * (1.0 - 1.0 * costs[paths_take[i_cost][j_cost]]);
					}
				} else {
					cout << paths_take[i_cost][j_cost] << " ";
					cur_cost = 1.0 - 1.0 * (1.0 - cur_cost) * (1.0 - 1.0 * costs[paths_take[i_cost][j_cost]]);
				}

				//cur_cost = 1.0 - 1.0 * (1.0 - cur_cost) * (1.0 - 1.0 * costs[paths_take[i_cost][j_cost]]);

			}
			paths_take_cost[i_cost] = cur_cost;
			cout << t << endl;

			cost *= cur_cost;
		}

		cout << "Cost: " << fixed << cost << endl;
		flow += addflow;
		numbFound = paths_take.size();
	}
    return paths_take;
}

void read_data(string s)
{
    ifstream fin(s);
    if (!fin.is_open()) {
        cout << "Cannot open file";
        return;
    }

    double tmp;
    int a, b;
    fin >> n >> m >> n_paths >> target >> t; //кол-во вершин, ребер, нужных путей, нужная вероятность, получатель

    fin >> n_routers >> n_links; //кол-во добавляемых коммутаторов и связей

    for (int i = 0; i < n; ++i) { //вероятности существующих коммутаторов
        fin >> tmp;
        costs.push_back(tmp);
    }

    for (int i = 0; i < n_routers; ++i) { //вероятности добавляемых коммутаторов
        fin >> tmp;
        p_router.push_back(tmp);
    }

    pair<int, int> edges[m];
    for (int i = 0; i < m; ++i) { //добавляем ребра
        fin >> a >> b;
        edges[i].first = a;
        edges[i].second = b;
        if (graph.find(a) != graph.end()) {
            graph[a].push_back(b);
        } else {
            vector<int> tmp_b(1, b);
            graph.insert(pair < int, vector<int> >(a, tmp_b));
        }
        if (graph.find(b) != graph.end()) {
            graph[b].push_back(a);
        } else {
            vector<int> tmp_a(1, a);
            graph.insert(pair < int, vector<int> >(b, tmp_a));
        }
    }
    to_orient_graph(n, m, edges);

    start_graph = graph;

    fin.close();
}

int min_joint()
{
    set<int> gs;
    set<int> gt;
    set<int> min_arr, joint_arr;
    gs.insert(0);

    for (map<int, vector<int>>::iterator i_t = graph.begin(); i_t != graph.end(); ++i_t) {
        gt.insert(i_t->first);
    }
    gt.erase(0);

    while (gt.size() > 1) {
        set<int> tmp_gs(gs);
        for (set<int>::iterator i = tmp_gs.begin(); i != tmp_gs.end(); ++i) {
            for (int j = 0; j < graph[*i].size(); ++j) {
                gs.insert(graph[*i][j]);
                gt.erase(graph[*i][j]);
            }
        }
        if (gt.size() < 1) {
            return min_arr.size();
        }

        joint_arr.clear();
        for (set<int>::iterator i = gs.begin(); i != gs.end(); ++i) {
            for (int j = 0; j < graph[*i].size(); ++j) {
                set<int>::iterator it = gs.find(graph[*i][j]);
                if (it == gs.end()) {
                    joint_arr.insert(*i);
                    break;
                }
            }
        }
        if (joint_arr.size() < min_arr.size() || min_arr.empty()) {
            min_arr = joint_arr;
        }
    }
    return min_arr.size();
}

void add_r_l(int add_links, int iter)
{
    g.resize(g.size()+2);
    n += 2;
    int in = g.size() - 2;
    int out = g.size() - 1;
    costs.push_back(p_router[iter]);
    costs.push_back(in_out_cost);
    vector<int> tmp;
    graph.insert(pair<int, vector<int>>(in, tmp));
    n_links -= add_links;
    add_rib(g, s, in, 1, costs[in], iter);
    add_rib(g, out, t, 1, costs[t], iter);
    graph[in].push_back(s);
    graph[in].push_back(t);
    graph[s].push_back(in);
    graph[t].push_back(in);
    m += 2;
    add_links -= 2;
    for (int j = 1; j < in_verts.size(); ++j) {
        add_rib(g, out_verts[j], in, 1, costs[in], iter);
        add_rib(g, out, in_verts[j], 1, costs[in_verts[j]], iter);
        graph[in].push_back(in_verts[j]);
        graph[in_verts[j]].push_back(in);
        add_links--;
        m += 2;
        if (!add_links) {
            break;
        }
    }
    add_rib(g, in, out, 1, in_out_cost, iter);
    m++;
    in_verts.push_back(in);
    out_verts.push_back(out);
}

void delete_link(int path_num)
{
    int j = 0;
    bool fl = false;
    while (!fl && j < paths[path_num].size()-1) {
        int out = paths[path_num][j];
        int in = out;
        int in2, out2;
        if (out != s) {
            out = paths[path_num][j+1];
            in2 = paths[path_num][j+2];
            j += 2;
        } else {
            in2 = paths[path_num][j+1];
            ++j;
        }
        if (in2 == t) {
            out2 = in2;
        } else {
            out2 = paths[path_num][j+1];
        }
        vector <rib> & a = g[out];
        for (vector <rib>::iterator i_t = a.begin(); i_t != a.end(); ++i_t) {
            if (i_t->b == in2 && i_t->iter != -1) {
                if (out == s) {
                    if (graph[s].size()-1 < n_paths) {
                        cout << "delete_link: graph[s].size() < n_paths\n";
                        break;
                    } else {
                        a.erase(i_t);
                        for (vector <rib>::iterator i_t1 = g[in2].begin(); i_t1 < g[in2].end(); ++i_t1) {
                            if (i_t1->b == out) {
                                g[in2].erase(i_t1);
                                break;
                            }
                        }
                        --m;
                        for (vector <int>::iterator i_t1 = graph[out].begin(); i_t1 < graph[out].end(); ++i_t1) {
                            if (*i_t1 == in2) {
                                graph[out].erase(i_t1);
                                break;
                            }
                        }
                        for (vector <int>::iterator i_t1 = graph[in2].begin(); i_t1 < graph[in2].end(); ++i_t1) {
                            if (*i_t1 == out) {
                                graph[in2].erase(i_t1);
                                break;
                            }
                        }
                        fl = true;
                        break;
                    }
                } else if (in2 == t) {
                    a.erase(i_t);
                    for (vector <rib>::iterator i_t1 = g[t].begin(); i_t1 < g[t].end(); ++i_t1) {
                        if (i_t1->b == out) {
                            g[t].erase(i_t1);
                            break;
                        }
                    }
                    --m;
                    for (vector <int>::iterator i_t1 = graph[in].begin(); i_t1 < graph[in].end(); ++i_t1) {
                        if (*i_t1 == t) {
                            graph[in].erase(i_t1);
                            break;
                        }
                    }
                    for (vector <int>::iterator i_t1 = graph[t].begin(); i_t1 < graph[t].end(); ++i_t1) {
                        if (*i_t1 == in) {
                            graph[t].erase(i_t1);
                            break;
                        }
                    }
                    fl = true;
                    break;
                } else {
                    a.erase(i_t);
                    for (vector <rib>::iterator i_t1 = g[in2].begin(); i_t1 < g[in2].end(); ++i_t1) {
                        if (i_t1->b == out) {
                            g[in2].erase(i_t1);
                            break;
                        }
                    }
                    --m;
                    for (vector <rib>::iterator i_t1 = g[out2].begin(); i_t1 < g[out2].end(); ++i_t1) {
                        if (i_t1->b == in) {
                            g[out2].erase(i_t1);
                            break;
                        }
                    }
                    for (vector <rib>::iterator i_t1 = g[in].begin(); i_t1 < g[in].end(); ++i_t1) {
                        if (i_t1->b == out2) {
                            g[in].erase(i_t1);
                            break;
                        }
                    }
                    --m;
                    for (vector <int>::iterator i_t1 = graph[in].begin(); i_t1 < graph[in].end(); ++i_t1) {
                        if (*i_t1 == in2) {
                            graph[in].erase(i_t1);
                            break;
                        }
                    }
                    for (vector <int>::iterator i_t1 = graph[in2].begin(); i_t1 < graph[in2].end(); ++i_t1) {
                        if (*i_t1 == in) {
                            graph[in2].erase(i_t1);
                            break;
                        }
                    }
                    fl = true;
                    break;
                }
            }
        }
    }
    if (!fl) {
        int in2 = paths[path_num][1];
        int in = s;
        for (vector <rib>::iterator i_t = g[in].begin(); i_t != g[in].end(); ++i_t) {
            if (i_t->b == in2) {
                g[in].erase(i_t);
                break;
            }
        }
        for (vector <rib>::iterator i_t = g[in2].begin(); i_t != g[in2].end(); ++i_t) {
            if (i_t->b == in) {
                g[in2].erase(i_t);
                break;
            }
        }
        --m;
        for (vector <int>::iterator i_t1 = graph[in].begin(); i_t1 < graph[in].end(); ++i_t1) {
            if (*i_t1 == in2) {
                graph[in].erase(i_t1);
                break;
            }
        }
        for (vector <int>::iterator i_t1 = graph[in2].begin(); i_t1 < graph[in2].end(); ++i_t1) {
            if (*i_t1 == in) {
                graph[in2].erase(i_t1);
                break;
            }
        }
        fl = true;
    }
}

void f_to_null()
{
    for (int i = 0; i < g.size(); ++i) {
        for (int j = 0; j < g[i].size(); ++j) {
            g[i][j].f = 0;
        }
    }
}

int greedy_alg()
{
    int i = 0; // iteration
    size_t sz = graph.size();
    while (cur_paths < n_paths || target < cost) {
        if (n_links == 0 || p_router.size() <= i) {
            cout << "routers or links are ended\n";
            return -1;
        }
        int add_links = (n_links < sz ? n_links : sz);

        add_r_l(add_links, i);
        ++i;

        int min_arr = min_joint();
        if (min_arr < n_paths) {
            cout << "min joint array is short\n";
            continue;
        }

        int path_len = 0;
        int path_num;
        while (path_len < min_path_len) {
            f_to_null();

            paths = search_path();

            cur_paths = paths.size();

            if (cur_paths < n_paths || target < cost) {
                cout << "if not passed\n";
                break;
            }

            paths_to_real_paths();
            path_len = (cur_paths ? real_paths[0].size() : 0);
            path_num = 0;
            for (int j = 1; j < cur_paths; ++j) {
                if (path_len > real_paths[j].size()) {
                    path_len = real_paths[j].size();
                    path_num = j;
                }
            }

            if (path_len < min_path_len) { // delete short path
                cout << "found short path\n";
                delete_link(path_num);
            }
        }
    }
    return 0;
}

void delete_wrong_links()
{
    for (int i = 0; i < real_paths.size(); ++i) {
        for (int j = 0; j < real_paths[i].size() - 1; ++j) {
            map < int, vector<int> >::iterator i_t = start_graph.find(real_paths[i][j]);
            if (i_t != start_graph.end()) {
                int a = real_paths[i][j];
                bool fl = false;
                for (int i1 = 0; i1 < start_graph[a].size(); ++i1) {
                    if (start_graph[a][i1] == real_paths[i][j+1]) {
                        fl = true;
                        break;
                    }
                }
                if (!fl) {
                    start_graph[a].push_back(real_paths[i][j+1]);
                }
            } else {
                start_graph.insert(pair<int, vector<int>>(real_paths[i][j], vector<int>(1, real_paths[i][j+1])));
            }

            i_t = start_graph.find(real_paths[i][j+1]);
            if (i_t != start_graph.end()) {
                int a = real_paths[i][j+1];
                bool fl = false;
                for (int i1 = 0; i1 < start_graph[a].size(); ++i1) {
                    if (start_graph[a][i1] == real_paths[i][j]) {
                        fl = true;
                        break;
                    }
                }
                if (!fl) {
                    start_graph[a].push_back(real_paths[i][j]);
                }
            } else {
                start_graph.insert(pair<int, vector<int>>(real_paths[i][j+1], vector<int>(1, real_paths[i][j])));
            }
        }
    }
}

void write_data(string s)
{
    int pos = s.find('.');
    s = s.insert(pos, "_answer");
    ofstream fout(s);
    fout << "Network:\n\n";
    for (map<int, vector<int>>::iterator i_t = start_graph.begin(); i_t != start_graph.end(); ++i_t) {
        fout << i_t->first << ' ';
        vector<int> tmp(i_t->second);
        for (vector<int>::iterator j_t = tmp.begin(); j_t != tmp.end(); ++j_t) {
            fout << *j_t << ' ';
        }
        fout << endl;
    }
    fout << "\n\nPaths:\n\n";
    for (int i = 0; i < real_paths.size(); ++i) {
        for (int j = 0; j < real_paths[i].size(); ++j) {
            fout << real_paths[i][j] << ' ';
        }
        fout << endl;
    }
    fout << "\nCost = " << cost << endl;
    fout.close();
}

int main()
{
    //read data and initialize
    string s;
    cout << "Enter input file\n";
    cin >> s;

    read_data(s);

    time_t time1, time2;
    time1 = clock();
    sort(p_router.begin(), p_router.end());
    //search_path
    paths = search_path();
    cur_paths = paths.size();

    paths_to_real_paths();

    min_path_len = (cur_paths ? real_paths[0].size() : 0);
    for (int j = 1; j < cur_paths; ++j) {
        if (min_path_len > real_paths[j].size()) {
            min_path_len = real_paths[j].size();
        }
    }

    int res = greedy_alg();
    if (res == -1) {
        cout << "Cannot build network\n";
        time2 = clock();
        cout << "time = " << time2-time1 << ' ' <<  time1 << ' ' << time2 << endl;
        return 0;
    }

    delete_wrong_links();
    time2 = clock();

    cout << "time = " << time2-time1 << ' ' <<  time1 << ' ' << time2 << endl;

    write_data(s);

    return 0;
}
