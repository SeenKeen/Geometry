# Geometry

### Bentley-Ottmann algorithm

BO is geometrical algorithm for finding all pairwise segment intersections. It's original complexity is O((n + K)logn), where K is number of intersections. Thus it does not make much sense if there are lots of intersectoins.

Here is implemented version searching just for any intersection, K = 1, so gained O(nlogn).

### Closest points pair
