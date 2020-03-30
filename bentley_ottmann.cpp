//  Copyright [2020] <Grulyov Denis>

// Bentley-Ottman algorithm
// Algorithm employs sweep line technique
// to find any pair of intersecting segments

// This code provides stable and fast implementation
// WITHOUT floating point arithmetics


#include <cmath>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <functional>
#include <set>
#include <stack>
#include <utility>
#include <vector>
using std::abs;
using std::cin;
using std::cout;
using std::function;
using std::max;
using std::min;
using std::pair;
using std::rand;
using std::set;
using std::sort;
using std::swap;
using std::vector;

struct point {
    int x__;
    int y__;
    point() {
        x__ = y__ = 0;
    }
    point(int x__, int y__) {
        this->x__ = x__;
        this->y__ = y__;
    }
    int64_t product(const point & to__, const point & check__) const {
        int64_t vx = to__.x__ - x__;
        int64_t vy = to__.y__ - y__;
        int64_t chx = check__.x__ - x__;
        int64_t chy = check__.y__ - y__;
        return vx * chy - chx * vy;
    }
    int det_sign(const point & to__, const point & check__) const {
        int64_t det = product(to__, check__);
        return (det != 0) ? (det / abs(det)) : 0;
    }
    bool operator == (const point & p__) const {
        return x__ == p__.x__ && y__ == p__.y__;
    }
};

struct segment {
    point p1__;
    point p2__;
    segment() {
        // None
    }
    segment(const point & p1__, const point & p2__) {
        if (p1__.x__ <= p2__.x__) {
            this->p1__ = p1__;
            this->p2__ = p2__;
        } else {
            this->p1__ = p2__;
            this->p2__ = p1__;
        }
        if (vertical() && (p1__.y__ > p2__.y__)) {
            swap(this->p1__.y__, this->p2__.y__);
        }
    }
    bool vertical() const {
        return p1__.x__ == p2__.x__;
    }
};

bool intersect(const segment & s1__, const segment & s2__) {
    if ((max(s1__.p1__.x__, s2__.p1__.x__) <=
         min(s1__.p2__.x__, s2__.p2__.x__)) &&
        min(max(s1__.p1__.y__, s1__.p2__.y__),
            max(s2__.p1__.y__, s2__.p2__.y__)) >=
        max(min(s1__.p1__.y__, s1__.p2__.y__),
            min(s2__.p1__.y__, s2__.p2__.y__))) {
        int s1_to_start = s1__.p1__.det_sign(s1__.p2__, s2__.p1__);
        int s1_to_end = s1__.p1__.det_sign(s1__.p2__, s2__.p2__);
        int s2_to_start = s2__.p1__.det_sign(s2__.p2__, s1__.p1__);
        int s2_to_end = s2__.p1__.det_sign(s2__.p2__, s1__.p2__);
        return s1_to_start * s1_to_end <= 0 &&
               s2_to_start * s2_to_end <= 0;
    }
    return false;
}

struct event {
    int id;
    int x__;
    char type;
    event() {
        // None
    }
    event(int id, int x__, char type) {
        this->id = id;
        this->x__ = x__;
        this->type = type;
    }
    bool operator < (const event & e__) const {
        return x__ < e__.x__ ||
               (x__ == e__.x__ && type == '+' && e__.type != '+');
    }
};

pair<int, int> find_intersection(const vector<segment> & segs) {
    vector<event> events;
    for (int i = 0; i < segs.size(); ++i) {
        events.emplace_back(i, segs[i].p1__.x__, '+');
        events.emplace_back(i, segs[i].p2__.x__, '-');
    }
    sort(events.begin(), events.end());
    auto y_order_pred =
            function<bool(int, int) >(
                    [&] (int idl__, int idr__) -> bool {
                        int desc_mask =
                                segs[idl__].vertical() + segs[idr__].vertical() * 2;
                        switch (desc_mask) {
                            case 3:
                            return segs[idl__].p2__.y__ < segs[idr__].p1__.y__;
                            case 2:
                            return segs[idl__].p1__.product(segs[idl__].p2__,
                                                            segs[idr__].p1__) > 0;
                            case 1:
                            return segs[idr__].p1__.product(segs[idr__].p2__,
                                                            segs[idl__].p1__) < 0;
                            default:
                            if (segs[idl__].p1__.x__ > segs[idr__].p1__.x__) {
                                return
                                        segs[idr__].p1__.product(segs[idr__].p2__,
                                                                 segs[idl__].p1__) < 0;
                            } else {
                                return
                                        segs[idl__].p1__.product(segs[idl__].p2__,
                                                                 segs[idr__].p1__) > 0;
                            }
                        }
                    });
    set<int, function<bool(int, int)> > y_order(y_order_pred);
    for (auto & e__ : events) {
        if (e__.type == '+') {
            auto place = y_order.lower_bound(e__.id);
            if (place != y_order.end()) {
                if (intersect(segs[*place], segs[e__.id])) {
                    return { *place, e__.id };
                }
            }
            if (place != y_order.begin()) {
                auto prev = std::prev(place);
                if (intersect(segs[*prev], segs[e__.id])) {
                    return { *prev, e__.id };
                }
            }
            y_order.insert(e__.id);
        } else {
            auto place = y_order.find(e__.id);
            if (place != y_order.begin()) {
                auto prev = std::prev(place);
                if (intersect(segs[*prev], segs[e__.id])) {
                    return { *prev, e__.id };
                }
            }
            auto next = std::next(place);
            if (next != y_order.end()) {
                if (intersect(segs[*next], segs[e__.id])) {
                    return { *next, e__.id };
                }
            }
            y_order.erase(place);
        }
    }
    return { -1, -1 };
}


int main() {
    int _N;
    cin >> _N;
    vector<segment> segs(_N);
    for (int i = 0; i < _N; ++i) {
        int p1x, p1y, p2x, p2y;
        cin >> p1x >> p1y >> p2x >> p2y;
        segs[i] = segment(point(p1x, p1y), point(p2x, p2y));
    }
    auto ans = find_intersection(segs);
    if (ans == std::make_pair(-1, -1)) {
        cout << "NO";
    } else {
        cout << "YES\n";
        cout << ans.first + 1 << ' ' << ans.second + 1 << std::endl;
    }
    return 0;
}
