// Author: Mingcheng Chen (linyufly@gmail.com)

#include <cstdlib>
#include <cstdio>
#include <cstring>

#include <algorithm>
#include <map>

using namespace std;

typedef unsigned long long UInt64;

// const char *kInputFile = "bigSearch.txt";
// const char *kInputFile = "smallSearch.txt";
// const char *kInputFile = "trickySearch.txt";
const char *kInputFile = "mediumSearch.txt";
const char kWall = '%';
const char kStart = 'P';
const char kGoal = '.';

const int kMaxRow = 100;
const int kMaxCol = 100;
const int kMaxGoal = 400;
const int kMaxHeapSize = 20000000;

const int dire[4][2] = {{1, 0}, {0, 1}, {-1, 0}, {0, -1}};

const int inf = 0x7fffffff;

struct Bits {
  UInt64 long_bits_[4];

  Bits() {
    memset(long_bits_, 0, sizeof(UInt64) * 4);
  }

  void locate(int index, int *block, int *bit) const {
    *block = index / 64;
    *bit = index % 64;
  }

  bool has_bit(int index) const {
    int block, bit;
    locate(index, &block, &bit);
    return long_bits_[block] & (static_cast<UInt64>(1) << bit);
  }

  bool empty() const {
    return !long_bits_[0] && !long_bits_[1]
           && !long_bits_[2] && !long_bits_[3];
  }

  void set_bit(int index, bool on) {
    int block, bit;
    locate(index, &block, &bit);
    UInt64 pow = static_cast<UInt64>(1) << bit;
    if (on) {
      long_bits_[block] |= pow;
    } else if (long_bits_[block] & pow) {
      long_bits_[block] -= pow;
    }
  }

  bool operator < (const Bits &other) const {
    for (int p = 0; p < 4; p++) {
      if (long_bits_[p] != other.long_bits_[p]) {
        return long_bits_[p] < other.long_bits_[p];
      }
    }
    return false;
  }
};

struct Status {
  int curr_;
  Bits bits_;

  bool operator < (const Status &other) const {
    if (curr_ != other.curr_) {
      return curr_ < other.curr_;
    }
    return bits_ < other.bits_;
  }
};

struct Node {
  int g_, last_goal_, heap_index_;

  Node() {
  }

  Node(int g, int last_goal, int heap_index)
      : g_(g), last_goal_(last_goal), heap_index_(heap_index) {}
};

char maze[kMaxRow][kMaxCol];
int goal[kMaxGoal][2];
int dist[kMaxGoal][kMaxGoal];
int num_rows, num_cols;
int num_goals;
map<Bits, int> mst;
map<Status, Node> record;
Status heap[kMaxHeapSize];
int f_heap[kMaxHeapSize];
int heap_size;

int get_mst(const Bits &bits) {
  if (mst.find(bits) != mst.end()) {
    return mst[bits];
  }

  static int focus[kMaxGoal], min_cost[kMaxGoal];
  static bool used[kMaxGoal];
  int num_focus = 0;

  for (int id = 0; id < num_goals; id++) {
    if (bits.has_bit(id)) {
      focus[num_focus++] = id;
    }
  }

  for (int id = 0; id < num_focus; id++) {
    min_cost[id] = dist[focus[0]][focus[id]];
    used[id] = id < 1;
  }

  int answer = 0;

  for (int count = 1; count < num_focus; count++) {
    int next = -1;
    int opt_cost = inf;
    for (int id = 0; id < num_focus; id++) {
      if (!used[id] && min_cost[id] < opt_cost) {
        next = id;
        opt_cost = min_cost[id];
      }
    }

    answer += opt_cost;
    used[next] = true;

    for (int id = 0; id < num_focus; id++) {
      if (!used[id] && min_cost[id] > dist[focus[next]][focus[id]]) {
        min_cost[id] = dist[focus[next]][focus[id]];
      }
    }
  }

  return mst[bits] = answer;
}

int get_heuristic(const Status &status) {
  int mst = get_mst(status.bits_);
  int first_path = inf;
  for (int id = 0; id < num_goals; id++) {
    if (status.bits_.has_bit(id) && dist[status.curr_][id] < first_path) {
      first_path = dist[status.curr_][id];
    }
  }
  return first_path + mst;
}

bool outside(int r, int c) {
  return r < 0 || c < 0 || r >= num_rows || c >= num_cols;
}

void breadth_first_search(int steps[][kMaxCol], int start_r, int start_c) {
  static int queue[kMaxRow * kMaxCol][2];

  for (int r = 0; r < num_rows; r++) {
    for (int c = 0; c < num_cols; c++) {
      steps[r][c] = inf;
    }
  }

  queue[0][0] = start_r;
  queue[0][1] = start_c;
  steps[start_r][start_c] = 0;

  int head, tail;
  for (head = tail = 0; head <= tail; head++) {
    int curr_r = queue[head][0];
    int curr_c = queue[head][1];
    for (int d = 0; d < 4; d++) {
      int next_r = curr_r + dire[d][0];
      int next_c = curr_c + dire[d][1];

      if (outside(next_r, next_c) || maze[next_r][next_c] == kWall
          || steps[next_r][next_c] < inf) {
        continue;
      }

      steps[next_r][next_c] = steps[curr_r][curr_c] + 1;
      tail++;
      queue[tail][0] = next_r;
      queue[tail][1] = next_c;
    }
  }
}

void calculate_dist() {
  static int steps[kMaxRow][kMaxCol];

  for (int id = 0; id < num_goals; id++) {
    breadth_first_search(steps, goal[id][0], goal[id][1]);

    for (int other = 0; other < num_goals; other++) {
      dist[id][other] = steps[goal[other][0]][goal[other][1]];
    }
  }
}

void init() {
  FILE *fin = fopen(kInputFile, "r");

  fgets(maze[0], kMaxCol, fin);

  num_cols = strlen(maze[0]) - 1;
  maze[0][num_cols] = 0;

  for (int row = 1; ; row++) {
    if (!fgets(maze[row], kMaxCol, fin) || feof(fin) || !strlen(maze[row])) {
      num_rows = row;
      break;
    }
    maze[row][num_cols] = 0;
  }

  fclose(fin);

  printf("num_rows = %d, num_cols = %d\n", num_rows, num_cols);
  for (int r = 0; r < num_rows; r++) {
    printf("%s\n", maze[r]);
  }

  num_goals = 0;
  for (int r = 0; r < num_rows; r++) {
    for (int c = 0; c < num_cols; c++) {
      if (maze[r][c] == kGoal || maze[r][c] == kStart) {
        goal[num_goals][0] = r;
        goal[num_goals][1] = c;
        num_goals++;
      }
    }
  }

  printf("num_goals = %d\n", num_goals);

  calculate_dist();
}

void slip_up(int index) {
  while (index) {
    int parent = (index - 1) / 2;

    if (f_heap[parent] <= f_heap[index]) {
      break;
    }

    record[heap[parent]].heap_index_ = index;
    record[heap[index]].heap_index_ = parent;
    swap(heap[parent], heap[index]);
    swap(f_heap[parent], f_heap[index]);

    index = parent;
  }
}

void slip_down(int index) {
  while (index * 2 + 1 < heap_size) {
    int child = index * 2 + 1;
    if (child + 1 < heap_size && f_heap[child + 1] < f_heap[child]) {
      child++;
    }

    if (f_heap[child] >= f_heap[index]) {
      break;
    }

    record[heap[child]].heap_index_ = index;
    record[heap[index]].heap_index_ = child;
    swap(heap[child], heap[index]);
    swap(f_heap[child], f_heap[index]);

    index = child;
  }
}

Status pop(int *f_value) {
  Status result = heap[0];
  *f_value = f_heap[0];

  record[result].heap_index_ = -1;

  if (!--heap_size) {
    return result;
  }

  heap[0] = heap[heap_size];
  f_heap[0] = f_heap[heap_size];
  record[heap[0]].heap_index_ = 0;

  slip_down(0);

  return result;
}

void push(const Status &status, int f_value) {
  if (heap_size == kMaxHeapSize - 1) {
    printf("Heap overflow.\n");
    exit(0);
  }

  heap[heap_size] = status;
  f_heap[heap_size] = f_value;
  heap_size++;
  record[status].heap_index_ = heap_size - 1;

  slip_up(heap_size - 1);
}

void work() {
  Status start;
  for (int id = 0; id < num_goals; id++) {
    if (maze[goal[id][0]][goal[id][1]] == kStart) {
      start.curr_ = id;
    } else {
      start.bits_.set_bit(id, true);
    }
  }

  record[start] = Node(0, -1, 0);
  heap[0] = start;
  f_heap[0] = get_heuristic(start) * num_goals + (num_goals - 1);
  heap_size = 1;

  while (heap_size) {
    if (f_heap[0] / num_goals <= 123 || record.size() % 10000 == 0) {
      printf("record.size() = %d, heap_size = %d, min_f = (%d, %d)\n",
             static_cast<int>(record.size()), heap_size,
             f_heap[0] / num_goals, f_heap[0] % num_goals);
    }

    int curr_f;
    Status curr = pop(&curr_f);
    Node curr_node = record[curr];
    int num_remaining = curr_f % num_goals;

    if (curr.bits_.empty()) {
      printf("Solution found. The number of expanded nodes is %d. The cost is %d.\n",
             static_cast<int>(record.size()), record[curr].g_);
      break;
    }

    for (int id = 0; id < num_goals; id++) {
      if (!curr.bits_.has_bit(id)) {
        continue;
      }

      bool useless = false;

      for (int other = 0; other < num_goals; other++) {
        if (other != id && other != curr.curr_ && curr.bits_.has_bit(other)
            && dist[curr.curr_][id] == dist[curr.curr_][other]
                                       + dist[other][id]) {
          useless = true;
          break;
        }
      }

      if (useless) {
        continue;
      }

      Status next;
      next.curr_ = id;
      next.bits_ = curr.bits_;
      next.bits_.set_bit(id, false);

      int g_value = curr_node.g_ + dist[curr.curr_][id];

      int next_f = g_value + get_heuristic(next);
      if (next_f < curr_f / num_goals) {
        printf("Inconsistency found: %d, %d.\n", next_f, curr_f / num_goals);
        exit(0);
      }

      Node next_node;

      if (record.find(next) != record.end()) {
        next_node = record[next];
        if (next_node.g_ <= g_value) {
          continue;
        }

        if (next_node.heap_index_ == -1) {
          printf("Heap index error: %d, %d.\n", g_value, next_node.g_);
          printf("curr_f = (%d, %d)\n", curr_f / num_goals, curr_f % num_goals);
          printf("next_f = %d\n", next_f);
          exit(0);
        }

        f_heap[next_node.heap_index_] -= (next_node.g_ - g_value) * num_goals;
        record[next].g_ = g_value;
        slip_up(next_node.heap_index_);
      } else {
        record[next] = Node(g_value, id, -1);
        push(next, (g_value + get_heuristic(next)) * num_goals
                   + (num_remaining - 1));
      }
    }
  }
}

int main() {
  init();
  work();

  return 0;
}
