// git.status = clean, build.date = Mon Apr 20 11:27:36 PDT 2020, git.hash = df25c71
#include "parser.cpp"
#include "cassert"
void check_arr32(vector<double> a, vector<double> b) {
  
  for(int i = 0; i < 31; i++) {
    assert((abs((a[i] - b[i])) < 0.00000000000001));
  }
}
void check_arr16(vector<double> a, vector<double> b) {
  
  for(int i = 0; i < 15; i++) {
    assert((abs((a[i] - b[i])) < 0.00000000000001));
  }
}
/***************** Parse helpers  ******************/
/***************************************************/
void kernel(vector<double> real, vector<double> img, vector<double> real_twid, vector<double> img_twid, vector<double> gold_real, vector<double> gold_img, vector<double> gold_real_twid, vector<double> gold_img_twid) {
  
  int span = (32 >> 1);
  int log = 0;
  while((span != 0)) {
    int odd = span;
    while((odd < 32)) {
      #pragma HLS loop_tripcount avg=16
      odd = (odd | span);
      int even = (odd ^ span);
      double real_odd = real[odd];
      double img_odd = img[odd];
      //---
      double real_even = real[even];
      double img_even = img[even];
      double temp_r = (real_even + real_odd);
      double temp_i = (img_even + img_odd);
      //---
      real[odd] = (real_even - real_odd);
      img[odd] = (img_even - img_odd);
      //---
      real[even] = temp_r;
      img[even] = temp_i;
      int rootindex = ((even << log) & (32 - 1));
      dbg(11111111);
      dbg(even);
      dbg(log);
      dbg(rootindex);
      dbg(22222222);
      //---
      if ((rootindex != 0)) {
        dbg(0);
        double temp = ((real_twid[rootindex] * real[odd]) - (img_twid[rootindex] * img[odd]));
        img_odd = img[odd];
        //---
        img[odd] = ((real_twid[rootindex] * img_odd) + (img_twid[rootindex] * real[odd]));
        //---
        real[odd] = temp;
      } else {
        dbg(1);
      }
      odd = (odd + 1);
    }
    span = (span >> 1);
    log = (log + 1);
  }
  //---
  check_arr32(real, gold_real);
  check_arr32(img, gold_img);
  check_arr16(real_twid, gold_real_twid);
  check_arr16(img_twid, gold_img_twid);
}
int main(int argc, char** argv) {
  using namespace flattening;
  auto v = parse_data(argc, argv);;
  auto real = get_arg<n_dim_vec_t<double, 1>>("real", "double[]", v);
  auto img = get_arg<n_dim_vec_t<double, 1>>("img", "double[]", v);
  auto real_twid = get_arg<n_dim_vec_t<double, 1>>("real_twid", "double[]", v);
  auto img_twid = get_arg<n_dim_vec_t<double, 1>>("img_twid", "double[]", v);
  auto gold_real = get_arg<n_dim_vec_t<double, 1>>("gold_real", "double[]", v);
  auto gold_img = get_arg<n_dim_vec_t<double, 1>>("gold_img", "double[]", v);
  auto gold_real_twid = get_arg<n_dim_vec_t<double, 1>>("gold_real_twid", "double[]", v);
  auto gold_img_twid = get_arg<n_dim_vec_t<double, 1>>("gold_img_twid", "double[]", v);
  kernel(real, img, real_twid, img_twid, gold_real, gold_img, gold_real_twid, gold_img_twid);
  return 0;
}