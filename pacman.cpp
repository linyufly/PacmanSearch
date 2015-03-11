// Author: Mingcheng Chen (linyufly@gmail.com)

#include <cstdlib>
#include <cstdio>
#include <cstring>

#include <map>
#include <set>
#include <vector>

using namespace std;

const char *kInputFile = "bigSearch.txt";
const int kRowLimit = 100;
const int kColLimit = 100;
const int kGoalLimit = 400;
const int kHeapLimit = 1000000;

const int dire[4][2] = {{-1, 0}, {1, 0}, {0, -1}, {0, 1}};

struct Status {
  int *goals_;
  int num_goals_;

  Status() {
  }

  Status(const Status &value) {
    num_goals_ = value.num_goals_;

    goals_ = new int[num_goals_];
    memcpy(goals_, value.goals_, sizeof(int) * num_goals_);
  }

  Status &operator = (const Status &value) {
    num_goals_ = value.num_goals_;

    goals_ = new int[num_goals_];
    memcpy(goals_, value.goals_, sizeof(int) * num_goals_);

    return *this;
  }

  ~Status() {
    if (goals_) {
      delete [] goals_;
    }
  }
};

bool operator < (const Status &a, const Status &b) {
  if (a.num_goals_ != b.num_goals_) {
    return a.num_goals_ < b.num_goals_;
  }

  for (int goal = 0; goal < a.num_goals_; goal++) {
    if (a.goals_[goal] != b.goals_[goal]) {
      return a.goals_[goal] < b.goals_[goal];
    }
  }

  return false;
}

struct StatusData {
  int heap_index_;
  int h_, g_;
};

char maze[kRowLimit][kColLimit];
int step[kRowLimit][kColLimit];
int queue[kRowLimit * kColLimit][2];
int goals[kGoalLimit][2];
int dist[kGoalLimit][kGoalLimit];
int min_dist[kGoalLimit];
bool in_tree[kGoalLimit];
int num_rows, num_cols, num_goals;
map<const Status *, StatusData> record;
map<const Status *, int> minimum_spanning_trees;
map<const Status *, int> storage_index;
Status *heap[kHeapLimit];
int heap_weight[kHeapLimit];
int heap_size;
vector<Status> storage;

Status *get_status_pointer(const Status &status) {
  if (storage_index.find(&status) == storage_index.end()) {
    storage.push_back(status);
    storage_index[&storage[storage.size() - 1]] = storage.size() - 1;

    return &storage[storage.size() - 1];
  }

  return &storage[storage_index[&status]];
}

int get_minimum_spanning_tree(const Status &status) {
  if (minimum_spanning_trees.find(&status) != minimum_spanning_trees.end()) {
    return minimum_spanning_trees[&status];
  }

  for (int id = 0; id < status.num_goals_; id++) {
    min_dist[id] = dist[status.goals_[0]][status.goals_[id]];
    in_tree[id] = false;
  }

  min_dist[0] = 0;
  in_tree[0] = true;

  int answer = 0;

  for (int count = 1; count < status.num_goals_; count++) {
    int minimum_cost = -1;
    int candidate = -1;

    for (int id = 0; id < status.num_goals_; id++) {
      if (!in_tree[id]) {
        if (minimum_cost == -1 || min_dist[id] < minimum_cost) {
          minimum_cost = min_dist[id];
          candidate = id;
        }
      }
    }

    in_tree[candidate] = true;
    answer += minimum_cost;

    for (int id = 0; id < status.num_goals_; id++) {
      if (!in_tree[id]
          && min_dist[id]
          > dist[status.goals_[candidate]][status.goals_[id]]) {
        min_dist[id] = dist[status.goals_[candidate]][status.goals_[id]];
      }
    }
  }

  return minimum_spanning_trees[get_status_pointer(status)] = answer;
}

int heuristic(const Status &status) {
  if (!status.num_goals_) {
    return 0;
  }

  int answer = -1;
  for (int id = 1; id < status.num_goals_; id++) {
    int cost = dist[status.goals_[0]][status.goals_[id]];
    if (answer == -1 || answer > cost) {
      answer = cost;
    }
  }

  Status temp_status;
  temp_status.num_goals_ = status.num_goals_ - 1;
  temp_status.goals_ = status.goals_ + 1;

  answer += get_minimum_spanning_tree(temp_status);

  temp_status.goals_ = NULL;

  return answer;
}

bool outside(int row, int col) {
  return row < 0 || col < 0 || row >= num_rows || col >= num_cols;
}

void breadth_first_search(int start_row, int start_col) {
  for (int row = 0; row < num_rows; row++) {
    for (int col = 0; col < num_cols; col++) {
      step[row][col] = -1;
    }
  }

  int head, tail;
  step[start_row][start_col] = 0;
  queue[0][0] = start_row;
  queue[0][1] = start_col;

  for (head = tail = 0; head <= tail; head++) {
    int curr_row = queue[head][0];
    int curr_col = queue[head][1];

    for (int d = 0; d < 4; d++) {
      int next_row = curr_row + dire[d][0];
      int next_col = curr_col + dire[d][1];

      if (outside(next_row, next_col)
          || maze[next_row][next_col] == '%'
          || step[next_row][next_col] != -1) {
        continue;
      }

      step[next_row][next_col] = step[curr_row][curr_col] + 1;
      tail++;
      queue[tail][0] = next_row;
      queue[tail][1] = next_col;
    }
  }
}

void calculate_dist() {
  for (int goal_id = 0; goal_id < num_goals; goal_id++) {
    breadth_first_search(goals[goal_id][0], goals[goal_id][1]);

    for (int other_id = 0; other_id < num_goals; other_id++) {
      dist[goal_id][other_id] = step[goals[other_id][0]][goals[other_id][1]];
    }
  }

  while (true) {
    int a, b;
    scanf("%d %d", &a, &b);
    printf("%d, %d --> %d, %d: %d\n",
           goals[a][0], goals[a][1], goals[b][0], goals[b][1],
           dist[a][b]);
  }
}

void init() {
  FILE *fin = fopen(kInputFile, "r");

  fgets(maze[0], kColLimit, fin);
  num_cols = strlen(maze[0]) - 1;
  maze[0][num_cols] = 0;

  for (int row = 1; ; row++) {
    if (fgets(maze[row], kColLimit, fin) == NULL
        || strlen(maze[row]) != num_cols + 1 || feof(fin)) {
      num_rows = row;
      break;
    }
    maze[row][num_cols] = 0;
  }

  printf("num_rows = %d, num_cols = %d\n", num_rows, num_cols);
  printf("Maze:\n");
  for (int row = 0; row < num_rows; row++) {
    printf("%s\n", maze[row]);
  }

  num_goals = 0;
  for (int row = 0; row < num_rows; row++) {
    for (int col = 0; col < num_cols; col++) {
      if (maze[row][col] == '.' || maze[row][col] == 'P') {
        goals[num_goals][0] = row;
        goals[num_goals][1] = col;
        num_goals++;
      }
    }
  }

  printf("num_goals = %d\n", num_goals);

  calculate_dist();

  fclose(fin);
}

void slip_down(int position) {
  while (position * 2 + 1 < heap_size) {
    int child = position * 2 + 1;
    if (child + 1 < heap_size && heap_weight[child + 1] < heap_weight[child]) {
      child++;
    }
  }
}

int heap_push(const Status &status) {
  heap[heap_size++] = status;

  slip_up(heap_size - 1);
}

Status *heap_pop() {
  Status *answer = heap[0];

  heap[0] = heap[heap_size - 1];
  heap_size--;

  slip_down(0); 
}

void work() {
  int start = -1;
  for (int goal_id = 0; goal_id < num_goals; goal_id++) {
    if (maze[goals[goal_id][0]][goals[goal_id][1]] == 'P') {
      start = goal_id;
      break;
    }
  }

  Status start_status;
  start_status.num_goals_ = num_goals;
  start_status.goals_ = new int[num_goals];
  start_status.goals_[0] = start;

  int curr_pos = 1;
  for (int goal_id = 0; goal_id < num_goals; goal_id++) {
    if (goal_id != start) {
      start_status.goals_[curr_pos++] = goal_id;
    }
  }

  record[get_status_pointer(start_status)].heap_index_ = 0;
  record[get_status_pointer(start_status)].g_ = 0;
  record[get_status_pointer(start_status)].h_ = heuristic(start_status);

  heap[0] = &start_status;
  heap_weight[0] = record[&start_status].h_;
  heap_size = 1;

  while (heap_size) {
  }
}

int main() {
  init();
  work();

  return 0;
}
