/*
Name: Emam Samara
Student ID: 1220022
Section: 1
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include <stdarg.h>

#define MAX_CITIES 60
#define MAX_NAME 64
#define INF 1000000000

static int weights[MAX_CITIES][MAX_CITIES];
static char names[MAX_CITIES][MAX_NAME];
static int city_count = 0;

static int dijkstra_parent[MAX_CITIES];
static int dijkstra_dist[MAX_CITIES];
static int bfs_parent[MAX_CITIES];
static int bfs_dist[MAX_CITIES];
static int bfs_ok = 1;

static int last_source = -1;
static double last_time_dijkstra = 0.0;
static double last_time_bfs = 0.0;
static char last_output[16384];

static double now_ms(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1000000.0;
}

static void trim(char *s) {
    char *start = s;
    char *end;
    while (*start && isspace((unsigned char)*start)) {
        start++;
    }
    if (start != s) {
        memmove(s, start, strlen(start) + 1);
    }
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)*(end - 1))) {
        end--;
    }
    *end = '\0';
}

static int str_casecmp(const char *a, const char *b) {
    while (*a && *b) {
        int ca = tolower((unsigned char)*a);
        int cb = tolower((unsigned char)*b);
        if (ca != cb) {
            return ca - cb;
        }
        a++;
        b++;
    }
    return tolower((unsigned char)*a) - tolower((unsigned char)*b);
}

static void init_graph(void) {
    int i, j;
    for (i = 0; i < MAX_CITIES; i++) {
        for (j = 0; j < MAX_CITIES; j++) {
            weights[i][j] = 0;
        }
    }
    city_count = 0;
}

static int find_city(const char *name) {
    int i;
    for (i = 0; i < city_count; i++) {
        if (str_casecmp(names[i], name) == 0) {
            return i;
        }
    }
    return -1;
}

static int add_city(const char *name) {
    int idx = find_city(name);
    if (idx >= 0) {
        return idx;
    }
    if (city_count >= MAX_CITIES) {
        return -1;
    }
    strncpy(names[city_count], name, MAX_NAME - 1);
    names[city_count][MAX_NAME - 1] = '\0';
    return city_count++;
}

static int load_cities(const char *filename) {
    FILE *fp = fopen(filename, "r");
    char line[256];
    if (!fp) {
        return -1;
    }
    init_graph();
    while (fgets(line, sizeof(line), fp)) {
        char *a, *b, *c;
        char *extra;
        char *endptr;
        long w;
        line[strcspn(line, "\r\n")] = '\0';
        if (line[0] == '\0') {
            continue;
        }
        a = strtok(line, "#");
        b = strtok(NULL, "#");
        c = strtok(NULL, "#");
        extra = strtok(NULL, "#");
        if (!a || !b || !c || extra) {
            continue;
        }
        trim(a);
        trim(b);
        trim(c);
        if (c[0] == '\0') {
            continue;
        }
        w = strtol(c, &endptr, 10);
        if (*endptr != '\0' || w <= 0 || w > INF) {
            continue;
        }
        {
            int i = add_city(a);
            int j = add_city(b);
            if (i < 0 || j < 0) {
                fclose(fp);
                return -2;
            }
            if (weights[i][j] == 0 || w < weights[i][j]) {
                weights[i][j] = w;
                weights[j][i] = w;
            }
        }
    }
    fclose(fp);
    return 0;
}

static void compute_dijkstra(int src) {
    typedef struct {
        int v;
        int dist;
    } HeapNode;

    typedef struct {
        int size;
        int capacity;
        HeapNode *arr;
        int *pos;
    } MinHeap;

    MinHeap *heap;
    int i;

    for (i = 0; i < city_count; i++) {
        dijkstra_dist[i] = INF;
        dijkstra_parent[i] = -1;
    }
    dijkstra_dist[src] = 0;

    heap = (MinHeap *)malloc(sizeof(MinHeap));
    if (!heap) {
        return;
    }
    heap->size = city_count;
    heap->capacity = city_count;
    heap->arr = (HeapNode *)malloc(sizeof(HeapNode) * city_count);
    heap->pos = (int *)malloc(sizeof(int) * city_count);
    if (!heap->arr || !heap->pos) {
        free(heap->arr);
        free(heap->pos);
        free(heap);
        return;
    }

    for (i = 0; i < city_count; i++) {
        heap->arr[i].v = i;
        heap->arr[i].dist = dijkstra_dist[i];
        heap->pos[i] = i;
    }

    /* Heapify down from the last non-leaf to build the heap. */
    for (i = (heap->size - 1) / 2; i >= 0; i--) {
        int idx = i;
        while (1) {
            int smallest = idx;
            int left = 2 * idx + 1;
            int right = 2 * idx + 2;
            if (left < heap->size && heap->arr[left].dist < heap->arr[smallest].dist) {
                smallest = left;
            }
            if (right < heap->size && heap->arr[right].dist < heap->arr[smallest].dist) {
                smallest = right;
            }
            if (smallest != idx) {
                HeapNode tmp = heap->arr[idx];
                heap->arr[idx] = heap->arr[smallest];
                heap->arr[smallest] = tmp;
                heap->pos[heap->arr[idx].v] = idx;
                heap->pos[heap->arr[smallest].v] = smallest;
                idx = smallest;
            } else {
                break;
            }
        }
        if (i == 0) {
            break;
        }
    }

    while (heap->size > 0) {
        int u;
        int v;
        HeapNode root = heap->arr[0];
        HeapNode last = heap->arr[heap->size - 1];
        heap->arr[0] = last;
        heap->pos[last.v] = 0;
        heap->size--;
        heap->pos[root.v] = -1;

        {
            int idx = 0;
            while (1) {
                int smallest = idx;
                int left = 2 * idx + 1;
                int right = 2 * idx + 2;
                if (left < heap->size && heap->arr[left].dist < heap->arr[smallest].dist) {
                    smallest = left;
                }
                if (right < heap->size && heap->arr[right].dist < heap->arr[smallest].dist) {
                    smallest = right;
                }
                if (smallest != idx) {
                    HeapNode tmp = heap->arr[idx];
                    heap->arr[idx] = heap->arr[smallest];
                    heap->arr[smallest] = tmp;
                    heap->pos[heap->arr[idx].v] = idx;
                    heap->pos[heap->arr[smallest].v] = smallest;
                    idx = smallest;
                } else {
                    break;
                }
            }
        }

        u = root.v;
        if (root.dist == INF) {
            break;
        }
        for (v = 0; v < city_count; v++) {
            if (weights[u][v] > 0 && heap->pos[v] != -1) {
                int nd = dijkstra_dist[u] + weights[u][v];
                if (nd < dijkstra_dist[v]) {
                    int idx = heap->pos[v];
                    dijkstra_dist[v] = nd;
                    dijkstra_parent[v] = u;
                    heap->arr[idx].dist = nd;
                    while (idx > 0) {
                        int parent = (idx - 1) / 2;
                        if (heap->arr[idx].dist < heap->arr[parent].dist) {
                            HeapNode tmp = heap->arr[idx];
                            heap->arr[idx] = heap->arr[parent];
                            heap->arr[parent] = tmp;
                            heap->pos[heap->arr[idx].v] = idx;
                            heap->pos[heap->arr[parent].v] = parent;
                            idx = parent;
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }

    free(heap->arr);
    free(heap->pos);
    free(heap);
}

static void compute_bfs(int src) {
    /* Standard BFS to minimize number of edges (hops). */
    int queue[MAX_CITIES];
    int front = 0, rear = 0;
    int visited[MAX_CITIES];
    int i;
    for (i = 0; i < city_count; i++) {
        bfs_dist[i] = -1;
        bfs_parent[i] = -1;
        visited[i] = 0;
    }
    bfs_ok = 1;
    bfs_dist[src] = 0;
    visited[src] = 1;
    queue[rear++] = src;

    while (front < rear) {
        int u = queue[front++];
        int v;
        for (v = 0; v < city_count; v++) {
            /* Treat all edges as weight 1 for hop-minimizing BFS. */
            if (weights[u][v] > 0 && !visited[v]) {
                bfs_dist[v] = bfs_dist[u] + 1;
                bfs_parent[v] = u;
                visited[v] = 1;
                queue[rear++] = v;
            }
        }
    }
}

static int build_path(int parent[], int src, int dest, int path[]) {
    int len = 0;
    int v = dest;
    if (src == dest) {
        path[len++] = src;
        return len;
    }
    while (v != -1) {
        path[len++] = v;
        if (v == src) {
            break;
        }
        v = parent[v];
    }
    if (path[len - 1] != src) {
        return 0;
    }
    {
        int i;
        for (i = 0; i < len / 2; i++) {
            int tmp = path[i];
            path[i] = path[len - 1 - i];
            path[len - 1 - i] = tmp;
        }
    }
    return len;
}

static int path_cost(int path[], int len) {
    int total = 0;
    int i;
    for (i = 0; i < len - 1; i++) {
        total += weights[path[i]][path[i + 1]];
    }
    return total;
}

static void append_output(char *buf, size_t size, const char *fmt, ...) {
    va_list args;
    size_t len = strlen(buf);
    if (len >= size) {
        return;
    }
    va_start(args, fmt);
    vsnprintf(buf + len, size - len, fmt, args);
    va_end(args);
}

static void print_route(const char *label, int path[], int len, int cost, char *out, size_t out_size) {
    int i;
    append_output(out, out_size, "%s\n", label);
    if (len == 0) {
        append_output(out, out_size, "No path found.\n\n");
        return;
    }
    for (i = 0; i < len - 1; i++) {
        int w = weights[path[i]][path[i + 1]];
        append_output(out, out_size, "%s -> %s (%d km)\n", names[path[i]], names[path[i + 1]], w);
    }
    append_output(out, out_size, "Total cost: %d km\n\n", cost);
}

static int read_line(char *buf, size_t size) {
    if (!fgets(buf, (int)size, stdin)) {
        return 0;
    }
    buf[strcspn(buf, "\r\n")] = '\0';
    return 1;
}

static int get_city_from_user(const char *prompt) {
    char line[128];
    int idx;
    while (1) {
        printf("%s", prompt);
        if (!read_line(line, sizeof(line))) {
            return -1;
        }
        trim(line);
        if (line[0] == '\0') {
            continue;
        }
        idx = find_city(line);
        if (idx >= 0) {
            return idx;
        }
        printf("City not found. Try again.\n");
    }
}

int main(void) {
    int loaded = 0;
    int has_destination = 0;
    int choice;
    char line[32];

    last_output[0] = '\0';

    while (1) {
        printf("\nMenu:\n");
        printf("1. Load cities\n");
        printf("2. Enter source city\n");
        printf("3. Enter destination city\n");
        printf("4. Exit\n");
        printf("Choose: ");

        if (!read_line(line, sizeof(line))) {
            break;
        }
        choice = atoi(line);

        if (choice == 1) {
            int rc = load_cities("cities.txt");
            if (rc == 0) {
                loaded = 1;
                last_source = -1;
                printf("Loaded %d cities from cities.txt.\n", city_count);
            } else if (rc == -1) {
                printf("Failed to open cities.txt.\n");
            } else {
                printf("Too many cities in file.\n");
            }
        } else if (choice == 2) {
            if (!loaded) {
                printf("Please load cities first.\n");
                continue;
            }
            {
                int src = get_city_from_user("Enter source city: ");
                if (src < 0) {
                    continue;
                }
                {
                    double t1 = now_ms();
                    compute_dijkstra(src);
                    double t2 = now_ms();
                    compute_bfs(src);
                    double t3 = now_ms();
                    last_time_dijkstra = t2 - t1;
                    last_time_bfs = t3 - t2;
                }
                last_source = src;
                printf("Computed Dijkstra and BFS from %s.\n", names[src]);
                printf("Dijkstra time: %.3f ms, BFS time: %.3f ms\n", last_time_dijkstra, last_time_bfs);
            }
        } else if (choice == 3) {
            if (!loaded || last_source < 0) {
                printf("Please load cities and enter a source city first.\n");
                continue;
            }
            {
                int dest = get_city_from_user("Enter destination city: ");
                if (dest < 0) {
                    continue;
                }
                {
                    int path_dij[MAX_CITIES];
                    int path_bfs[MAX_CITIES];
                    int len_dij = 0;
                    int len_bfs = 0;
                    int has_dij = (dijkstra_dist[dest] != INF);
                    int has_bfs = (bfs_ok && bfs_dist[dest] != -1);
                    int cost_dij = has_dij ? dijkstra_dist[dest] : 0;
                    if (has_dij) {
                        len_dij = build_path(dijkstra_parent, last_source, dest, path_dij);
                    }
                    if (has_bfs) {
                        len_bfs = build_path(bfs_parent, last_source, dest, path_bfs);
                    }
                    int cost_bfs = (len_bfs > 0) ? path_cost(path_bfs, len_bfs) : 0;

                    last_output[0] = '\0';
                    append_output(last_output, sizeof(last_output), "Source: %s\n", names[last_source]);
                    append_output(last_output, sizeof(last_output), "Destination: %s\n\n", names[dest]);
                    append_output(last_output, sizeof(last_output), "Dijkstra time: %.3f ms\n", last_time_dijkstra);
                    append_output(last_output, sizeof(last_output), "BFS time: %.3f ms\n\n", last_time_bfs);
                    if (len_dij > 0) {
                        append_output(last_output, sizeof(last_output), "Minimum cost (Dijkstra): %d km\n", cost_dij);
                    } else {
                        append_output(last_output, sizeof(last_output), "Minimum cost (Dijkstra): N/A\n");
                    }
                    if (len_bfs > 0) {
                        append_output(last_output, sizeof(last_output), "Minimum hops (BFS): %d\n", bfs_dist[dest]);
                        append_output(last_output, sizeof(last_output), "BFS path cost: %d km\n\n", cost_bfs);
                    } else {
                        append_output(last_output, sizeof(last_output), "Minimum hops (BFS): N/A\n");
                        append_output(last_output, sizeof(last_output), "BFS path cost: N/A\n\n");
                    }

                    if (len_dij > 0) {
                        print_route("Dijkstra path:", path_dij, len_dij, cost_dij, last_output, sizeof(last_output));
                    } else {
                        append_output(last_output, sizeof(last_output), "Dijkstra path:\nNo path found.\n\n");
                    }
                    if (len_bfs > 0) {
                        print_route("BFS path:", path_bfs, len_bfs, cost_bfs, last_output, sizeof(last_output));
                    } else {
                        append_output(last_output, sizeof(last_output), "BFS path:\nNo path found.\n\n");
                    }

                    printf("%s", last_output);
                    has_destination = 1;
                }
            }
        } else if (choice == 4) {
            FILE *out;
            if (!has_destination) {
                printf("Please enter a destination city first (option 3).\n");
                continue;
            }
            if (last_output[0] == '\0') {
                printf("No route computed to save.\n");
                return 0;
            }
            out = fopen("shortest_path.txt", "w");
            if (!out) {
                printf("Failed to write shortest_path.txt.\n");
                return 0;
            }
            fputs(last_output, out);
            fclose(out);
            printf("Saved to shortest_path.txt.\n");
            return 0;
        } else {
            printf("Invalid choice.\n");
        }
    }
    return 0;
}
