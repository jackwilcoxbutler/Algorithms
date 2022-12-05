#include <iostream>
#include <bits/stdc++.h>
#include <queue>
#define INF 999
#define numPts 4


using namespace std;

struct Item{
    int profit;
    int weight;
    bool used;

    Item(int p, int w) : profit(p), weight(w)
    {used = false;}
};

struct node {
    int level;
    int profit;
    int weight;
    float bound;
    vector <int> k;
    
    bool operator<(const node &rhs) const{
        return (bound < rhs.bound);
    }
};

bool cmp(struct Item a, struct Item b)
{
    double r1 = (double)a.profit / a.weight;
    double r2 = (double)b.profit / b.weight;
    return r1 > r2;
}

int max(struct Item a, struct Item b){
    return a.profit > b.profit ? a.profit : b.profit;
}

void printMatrix(int matrix[][numPts]) {
  for (int i = 0; i < numPts; i++) {
    for (int j = 0; j < numPts; j++) {
      if (matrix[i][j] == INF)
        printf("%4s", "INF");
      else
        printf("%4d", matrix[i][j]);
    }
    printf("\n");
  }
}

void floyd(int graph[][numPts]) {
  int matrix[numPts][numPts], i, j, k;

  for (i = 0; i < numPts; i++)
    for (j = 0; j < numPts; j++)
      matrix[i][j] = graph[i][j];

  // Adding vertices individually
  for (k = 0; k < numPts; k++) {
    for (i = 0; i < numPts; i++) {
      for (j = 0; j < numPts; j++) {
        if (matrix[i][k] + matrix[k][j] < matrix[i][j])
          matrix[i][j] = matrix[i][k] + matrix[k][j];
      }
    }
  }
  printMatrix(matrix);
}

double greedyNoFrac(struct Item items[], int capacity, int size){
    int currentProfit = 0;
    int weight = 0;
    
    //sort items according to p/w
    sort(items,items + size, cmp);

    for(int i = 0; i < size; i++){
        if((capacity - weight) > items[i].weight){
            weight += items[i].weight;
            currentProfit += items[i].profit;
            items[i].used = true;
        }
    }

    return currentProfit;
}

double greedyWithFrac(struct Item items[], int capacity, int size){
    double profit = 0.0;
    int weight = 0;

    sort(items, items + size, cmp);

    for(int i = 0; i < size; i++){
        if(weight + items[i].weight < capacity){
            weight += items[i].weight;
            profit += items[i].profit;
        }else{
            int leftover = capacity - weight;
            profit += ((double)items[i].profit/items[i].weight) * leftover;
            break;
        }
    }
    return profit;
}

int KnapsackDP(int capacity, struct Item a[], int n){
    int weight;

    int X[n+1][capacity + 1];
    for(int i = 0; i <= n; i++){
        for(weight = 0; weight <= capacity; weight++){
            if(i == 0 || weight == 0){X[i][weight] = 0;} //base case
            else if(a[i-1].weight <= weight){
                X[i][weight] = max(a[i-1].profit + X[i-1][weight - a[i-1].weight],X[i-1][weight]);
            }else{
                X[i][weight] = X[i-1][weight];
            }
        }
    }
    return X[n][capacity];
}

//global variables for knapsack
int  weight, profit, maxprofit = 0,numItems = 5,numbest;
string bestset[5], include[5];
bool promising(int index,int weight, int profit, const struct Item z[], int capacity);

void resetTrackers(){
    for(int i = 0; i<= 5; i++){
        bestset[i] = "no";
        include[i] = "no";
    }
}

void KnapsackBT(int i, int profit, int weight, const struct Item z[],int capacity){
    if(weight <= capacity && profit > maxprofit){
        maxprofit = profit;
        numbest = i;
        for(int temp = 0; temp < numbest; temp++){
            bestset[i] = include[i];
        }
    }
    //cout << weight << "  " << profit <<endl; 
    if(promising(i,weight,profit,z,capacity)){
        include[i + 1] = "yes";
        //cout << i + 1 << ", " << profit + z[i+1].profit << ", " << weight + z[i+1].weight << endl;
        KnapsackBT(i+1, profit + z[i+1].profit, weight + z[i+1].weight,z,capacity);
        include[i + 1] = "no";
        //cout << i + 1 << ", " << profit << ", " << weight << endl;
        KnapsackBT(i+1, profit, weight,z, capacity);
    }
}

bool promising(int index,int weight, int profit, const struct Item z[], int capacity){
    //Calculating bound for not including first incorrectly.
    int j,k;
    int totweight;
    float bound;
    
    if(weight >= capacity){
        return false;
    }else{
        j = index + 1;
        bound = profit;
        totweight = weight;
        while( j <= numItems && (totweight + z[j].weight) <= capacity){
            totweight = totweight + z[j].weight;
            bound = bound + z[j].profit;
            j++;
        }
        if(j<=numItems){
            bound = bound + (capacity - totweight) * (z[j].profit/z[j].weight);
        }
        //cout << bound << " ||| " << index << endl;
        return bound > maxprofit;
    }

}

int KnapsackBB(int &best){
return 0;}

int main(int argc, char *argv[]){
    Item num33[] = {{20,2},{25,5},{35,7},{12,3},{3,1}};
    int cap33 = 9;
    Item num5[] = {{20,2},{30,5},{35,7},{12,3},{3,1}};
    int cap5 = 13;

    int graph[4][4] = {{0, 3, INF, 5},
             {2, 0, INF, 4},
             {INF, 1, 0, INF},
             {INF, INF, 2, 0}};
    cout << "Floyd's : " << endl;
    floyd(graph); cout << endl << endl;

    cout << "KNAPSACK : " << endl;
    cout << " No fractions #33: " << greedyNoFrac(num33, cap33, 5) << endl;
    cout << " No fractions #5: " << greedyNoFrac(num5, cap5, 5) << endl;

    cout << " Fractions #33 : " << greedyWithFrac(num33, cap33, 5) << endl;
    cout << " Fractions #5 : " << greedyWithFrac(num5, cap5, 5) << endl;

    cout << " Dynamic Programming #33: " << KnapsackDP(cap33,num33,5) << endl;
    cout << " Dynamic Programming #5: " << KnapsackDP(cap5,num5,5) << endl;

    //Test Knapsack backtrack with #33 from exercise 5
    numbest = 0;
    //resetTrackers();
    KnapsackBT(0,0,0,num33,9);
    cout << " BackTracking #33 : " << maxprofit << " using items : ";
    for(int k=0;k <= numbest; k++){
        if(bestset[k] == "yes"){
            cout << k + 1 << " ";
        }
    }cout << endl;

    //Test Knapsack backtrack with #1 from exercise 5
    resetTrackers();
    numbest = 0;
    KnapsackBT(0,0,0,num5,13);
    cout << " BackTracking #5 : " << maxprofit << " using items : ";
    for(int k=0;k <= numbest; k++){
        if(bestset[k] == "yes"){
            cout << k + 1 << " ";
        }
    }cout << endl;

    return 0;
}

