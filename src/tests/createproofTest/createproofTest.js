const axios = require('axios');

function main() {
  let hostCallEntryTable = require('./blspairtest.json');

  axios({
    methods: 'post',
    url: '/createproof',
    baseURL: 'http://127.0.0.1:8080/',
    data: {
    host_call_entry_table: JSON.parse(JSON.stringify(hostCallEntryTable)),
    opname: "BLS381PAIR",
    output_folder: "./result"
    }
  })
  .then(function(response) {
    console.log("response", response);
  })
  .catch(function(error) {
    console.log("error:", error);
  });
}

main();
